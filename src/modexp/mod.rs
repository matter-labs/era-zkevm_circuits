pub mod implementation;

// Testing packages
pub mod input;
#[cfg(test)]
pub mod test;
pub mod tests_json;

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};

use boojum::algebraic_props::round_function::AlgebraicRoundFunction;

use boojum::cs::gates::PublicInputGate;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;

use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::gadgets::u160::UInt160;
use boojum::gadgets::u2048::UInt2048;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use cs_derive::*;
use derivative::Derivative;
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

use crate::base_structures::log_query::*;
use crate::base_structures::memory_query::*;
use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::fsm_input_output::*;
use crate::modexp::implementation::u256::modexp_32_4_32;
use crate::modexp::input::{ModexpCircuitInputOutput, ModexpCircuitInstanceWitness};
use crate::storage_application::ConditionalWitnessAllocator;

use super::*;

pub const BASE_U256_SIZE: usize = 1; // 256
pub const EXP_U256_SIZE: usize = 1; // 32, but the evm slot is 256
pub const MOD_U256_SIZE: usize = 1; //  256

pub const MEMORY_QUERIES_PER_CALL: usize = BASE_U256_SIZE + EXP_U256_SIZE + MOD_U256_SIZE;
pub const NUM_MEMORY_READS_PER_CYCLE: usize = BASE_U256_SIZE + EXP_U256_SIZE + MOD_U256_SIZE;

#[derive(Derivative, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct ModexpPrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_offset: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_offset: UInt32<F>,
}

impl<F: SmallField> ModexpPrecompileCallParams<F> {
    pub fn from_encoding<CS: ConstraintSystem<F>>(_cs: &mut CS, encoding: UInt256<F>) -> Self {
        let input_offset = encoding.inner[0];
        let output_offset = encoding.inner[2];
        let input_page = encoding.inner[4];
        let output_page = encoding.inner[5];

        let new = Self {
            input_page,
            input_offset,
            output_page,
            output_offset,
        };

        new
    }
}

// Use this function in case you wish to update base or mod size from u256 to u2048 bits.
fn uint256s_to_u2048<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    values: [UInt256<F>; 8],
) -> UInt2048<F> {
    let mut u2048: UInt2048<F> = UInt2048::zero(cs);

    for (i, value) in values.iter().enumerate() {
        u2048.inner[i * 8..(i + 1) * 8].copy_from_slice(&value.inner);
    }

    u2048
}

// Use this function in case you wish to update base or mod size from u256 to u2048 bits.
fn uint2048_to_uint256s<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    value: UInt2048<F>,
) -> [UInt256<F>; 8] {
    let mut result: [UInt256<F>; 8] = core::array::from_fn(|_| UInt256::zero(cs));

    for (i, chunk) in result.iter_mut().enumerate() {
        chunk
            .inner
            .copy_from_slice(&value.inner[i * 8..(i + 1) * 8]);
    }

    result
}

fn modexp_precompile_inner<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    values: [UInt256<F>; NUM_MEMORY_READS_PER_CYCLE],
) -> (Boolean<F>, [UInt256<F>; MOD_U256_SIZE]) {
    let base: [UInt256<F>; BASE_U256_SIZE] = values[..BASE_U256_SIZE].try_into().unwrap();
    let exponent: [UInt256<F>; EXP_U256_SIZE] = values
        [BASE_U256_SIZE..BASE_U256_SIZE + EXP_U256_SIZE]
        .try_into()
        .unwrap();
    let modulus: [UInt256<F>; MOD_U256_SIZE] = values
        [BASE_U256_SIZE + EXP_U256_SIZE..BASE_U256_SIZE + EXP_U256_SIZE + MOD_U256_SIZE]
        .try_into()
        .unwrap();

    // This shall be edited if dimensions for something change:
    let base = base[0];
    let exponent = exponent[0].inner[0];
    let modulus = modulus[0];

    let success = Boolean::allocated_constant(cs, true);
    let result = modexp_32_4_32(cs, &base, &exponent, &modulus);

    (success, [result])
}

pub fn modexp_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: ModexpCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    let ModexpCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;
    let memory_reads_witness: VecDeque<_> = memory_reads_witness.into_iter().flatten().collect();

    let mut structured_input =
        ModexpCircuitInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
    let start_flag = structured_input.start_flag;

    let requests_queue_state_from_input = structured_input.observable_input.initial_log_queue_state;
    requests_queue_state_from_input.enforce_trivial_head(cs);

    let requests_queue_state_from_fsm = structured_input.hidden_fsm_input.log_queue_state;

    let requests_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &requests_queue_state_from_input,
        &requests_queue_state_from_fsm,
    );

    let mut requests_queue = StorageLogQueue::<F, R>::from_state(cs, requests_queue_state);
    let queue_witness = CircuitQueueWitness::from_inner_witness(requests_queue_witness);
    requests_queue.witness = Arc::new(queue_witness);

    let memory_queue_state_from_input =
        structured_input.observable_input.initial_memory_queue_state;
    memory_queue_state_from_input.enforce_trivial_head(cs);

    let memory_queue_state_from_fsm = structured_input.hidden_fsm_input.memory_queue_state;

    let memory_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &memory_queue_state_from_input,
        &memory_queue_state_from_fsm,
    );

    let mut memory_queue = MemoryQueue::<F, R>::from_state(cs, memory_queue_state);
    let read_queries_allocator = ConditionalWitnessAllocator::<F, UInt256<F>> {
        witness_source: Arc::new(RwLock::new(memory_reads_witness)),
    };

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::MODEXP_PRECOMPILE_FORMAL_ADDRESS,
    );

    let one_u32 = UInt32::allocated_constant(cs, 1u32);
    let zero_u256 = UInt256::zero(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    for _cycle in 0..limit {
        let is_empty = requests_queue.is_empty(cs);
        let should_process = is_empty.negated(cs);
        let (request, _) = requests_queue.pop_front(cs, should_process);

        let mut precompile_call_params = ModexpPrecompileCallParams::from_encoding(cs, request.key);

        let timestamp_to_use_for_read = request.timestamp;
        let timestamp_to_use_for_write = timestamp_to_use_for_read.add_no_overflow(cs, one_u32);

        Num::conditionally_enforce_equal(
            cs,
            should_process,
            &Num::from_variable(request.aux_byte.get_variable()),
            &Num::from_variable(aux_byte_for_precompile.get_variable()),
        );
        for (a, b) in request
            .address
            .inner
            .iter()
            .zip(precompile_address.inner.iter())
        {
            Num::conditionally_enforce_equal(
                cs,
                should_process,
                &Num::from_variable(a.get_variable()),
                &Num::from_variable(b.get_variable()),
            );
        }

        let mut read_values = [zero_u256; NUM_MEMORY_READS_PER_CYCLE];
        let mut bias_variable = should_process.get_variable();
        for dst in read_values.iter_mut() {
            let read_query_value = read_queries_allocator.conditionally_allocate_biased(
                cs,
                should_process,
                bias_variable,
            );
            bias_variable = read_query_value.inner[0].get_variable();

            *dst = read_query_value;

            let read_query = MemoryQuery {
                timestamp: timestamp_to_use_for_read,
                memory_page: precompile_call_params.input_page,
                index: precompile_call_params.input_offset,
                rw_flag: boolean_false,
                is_ptr: boolean_false,
                value: read_query_value,
            };

            let _ = memory_queue.push(cs, read_query, should_process);

            precompile_call_params.input_offset = precompile_call_params
                .input_offset
                .add_no_overflow(cs, one_u32);
        }

        if crate::config::CIRCUIT_VERSOBE {
            if should_process.witness_hook(cs)().unwrap() == true {
                for each in read_values.iter() {
                    dbg!(each.witness_hook(cs)());
                }
            }
        }

        let (success, v) = modexp_precompile_inner(cs, read_values);

        let success_as_u32 = unsafe { UInt32::from_variable_unchecked(success.get_variable()) };
        let mut success = zero_u256;
        success.inner[0] = success_as_u32;

        if crate::config::CIRCUIT_VERSOBE {
            if should_process.witness_hook(cs)().unwrap() == true {
                dbg!(success.witness_hook(cs)());
                for each in v.iter() {
                    dbg!(each.witness_hook(cs)());
                }
            }
        }

        let success_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            index: precompile_call_params.output_offset,
            rw_flag: boolean_true,
            is_ptr: boolean_false,
            value: success,
        };

        let _ = memory_queue.push(cs, success_query, should_process);
        precompile_call_params.output_offset = precompile_call_params
            .output_offset
            .add_no_overflow(cs, one_u32);

        for v_u256 in v {
            let v_u256_query = MemoryQuery {
                timestamp: timestamp_to_use_for_write,
                memory_page: precompile_call_params.output_page,
                index: precompile_call_params.output_offset,
                rw_flag: boolean_true,
                is_ptr: boolean_false,
                value: v_u256,
            };

            let _ = memory_queue.push(cs, v_u256_query, should_process);
            precompile_call_params.output_offset = precompile_call_params
                .output_offset
                .add_no_overflow(cs, one_u32);
        }
    }

    requests_queue.enforce_consistency(cs);

    let done = requests_queue.is_empty(cs);
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::placeholder(cs);

    let final_memory_state = memory_queue.into_state();
    let final_requests_state = requests_queue.into_state();

    structured_input.observable_output.final_memory_state = QueueState::conditionally_select(
        cs,
        structured_input.completion_flag,
        &final_memory_state,
        &structured_input.observable_output.final_memory_state,
    );

    structured_input.hidden_fsm_output.log_queue_state = final_requests_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    structured_input.hook_compare_witness(cs, &closed_form_input);

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);
    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}
