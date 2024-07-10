use arrayvec::ArrayVec;

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
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::pairing::bn256;
use cs_derive::*;
use derivative::Derivative;
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

use crate::base_structures::log_query::*;
use crate::base_structures::memory_query::*;
use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::bn254::ec_pairing::input::{EcPairingCircuitInputOutput, EcPairingFunctionFSM};
use crate::bn254::validation::{
    is_affine_infinity, is_on_curve, is_on_twist_curve, is_twist_affine_infinity, validate_in_field,
};
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::fsm_input_output::*;
use crate::storage_application::ConditionalWitnessAllocator;
use boojum::cs::Variable;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::tower_extension::fq12::Fq12;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::encodable::CircuitVarLengthEncodable;

use super::*;

use self::ec_mul::implementation::convert_uint256_to_field_element;
use self::implementation::ec_pairing;
use self::input::EcPairingCircuitInstanceWitness;

pub mod final_exp;
pub mod implementation;
pub mod input;

pub const NUM_MEMORY_READS_PER_CYCLE: usize = 6;
pub const EXCEPTION_FLAGS_ARR_LEN: usize = 8;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct EcPairingPrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_offset: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_offset: UInt32<F>,
    pub num_pairs: UInt32<F>,
}

impl<F: SmallField> CSPlaceholder<F> for EcPairingPrecompileCallParams<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_u32 = UInt32::zero(cs);
        Self {
            input_page: zero_u32,
            input_offset: zero_u32,
            output_page: zero_u32,
            output_offset: zero_u32,
            num_pairs: zero_u32,
        }
    }
}

impl<F: SmallField> EcPairingPrecompileCallParams<F> {
    pub fn from_encoding<CS: ConstraintSystem<F>>(_cs: &mut CS, encoding: UInt256<F>) -> Self {
        let input_offset = encoding.inner[0];
        let output_offset = encoding.inner[2];
        let input_page = encoding.inner[4];
        let output_page = encoding.inner[5];
        let num_pairs = encoding.inner[6];

        let new = Self {
            input_page,
            input_offset,
            output_page,
            output_offset,
            num_pairs,
        };

        new
    }
}

fn pair<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    p_x: &mut UInt256<F>,
    p_y: &mut UInt256<F>,
    q_x_c0: &mut UInt256<F>,
    q_x_c1: &mut UInt256<F>,
    q_y_c0: &mut UInt256<F>,
    q_y_c1: &mut UInt256<F>,
) -> (Boolean<F>, BN256Fq12NNField<F>) {
    let base_field_params = &Arc::new(bn254_base_field_params());

    // We need to check for infinity prior to potential masking coordinates.
    let p_is_infinity = is_affine_infinity(cs, (&p_x, &p_y));
    let q_is_infinity = is_twist_affine_infinity(cs, (&q_x_c0, &q_x_c1, &q_y_c0, &q_y_c1));

    let coordinates_are_in_field = validate_in_field(
        cs,
        &mut [p_x, p_y, q_x_c0, q_x_c1, q_y_c0, q_y_c1],
        base_field_params,
    );

    let p_x = convert_uint256_to_field_element(cs, &p_x, base_field_params);
    let p_y = convert_uint256_to_field_element(cs, &p_y, base_field_params);

    let p_on_curve = is_on_curve(cs, (&p_x, &p_y), base_field_params);
    let p_is_valid = p_on_curve.or(cs, p_is_infinity);

    // Mask the point with zero in case it is not on curve.
    let zero = BN256SWProjectivePoint::zero(cs, base_field_params);
    let unchecked_point = BN256SWProjectivePoint::from_xy_unchecked(cs, p_x, p_y);
    let mut p =
        BN256SWProjectivePoint::conditionally_select(cs, p_on_curve, &unchecked_point, &zero);

    let q_x_c0 = convert_uint256_to_field_element(cs, &q_x_c0, base_field_params);
    let q_x_c1 = convert_uint256_to_field_element(cs, &q_x_c1, base_field_params);
    let q_y_c0 = convert_uint256_to_field_element(cs, &q_y_c0, base_field_params);
    let q_y_c1 = convert_uint256_to_field_element(cs, &q_y_c1, base_field_params);

    let q_x = BN256Fq2NNField::new(q_x_c0, q_x_c1);
    let q_y = BN256Fq2NNField::new(q_y_c0, q_y_c1);

    let q_on_curve = is_on_twist_curve(cs, (&q_x, &q_y), base_field_params);
    let q_is_valid = q_on_curve.or(cs, q_is_infinity);

    // Mask the point with zero in case it is not on curve.
    let zero = BN256SWProjectivePointTwisted::zero(cs, base_field_params);
    let unchecked_point = BN256SWProjectivePointTwisted::from_xy_unchecked(cs, q_x, q_y);
    let mut q = BN256SWProjectivePointTwisted::conditionally_select(
        cs,
        q_on_curve,
        &unchecked_point,
        &zero,
    );

    let result = ec_pairing(cs, &mut p, &mut q);

    let mut exception_flags = ArrayVec::<_, EXCEPTION_FLAGS_ARR_LEN>::new();
    exception_flags.extend(coordinates_are_in_field);
    exception_flags.push(p_is_valid);
    exception_flags.push(q_is_valid);

    let any_exception = Boolean::multi_or(cs, &exception_flags[..]);
    let result = result.mask_negated(cs, any_exception);
    let success = any_exception.negated(cs);

    (success, result)
}

pub fn ecpairing_precompile_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    memory_queue: &mut MemoryQueue<F, R>,
    precompile_calls_queue: &mut StorageLogQueue<F, R>,
    memory_read_witness: ConditionalWitnessAllocator<F, UInt256<F>>,
    mut state: EcPairingFunctionFSM<F>,
    _round_function: &R,
    limit: usize,
) -> EcPairingFunctionFSM<F>
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    assert!(limit <= u32::MAX as usize);

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::ECPAIRING_PRECOMPILE_FORMAL_ADDRESS,
    );
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);
    let zero_u256 = UInt256::zero(cs);
    let one_fq12 = BN256Fq12NNField::one(cs, &Arc::new(bn254_base_field_params()));

    // we can have a degenerate case when queue is empty, but it's a first circuit in the queue,
    // so we taken default FSM state that has state.read_precompile_call = true;
    let input_queue_is_empty = precompile_calls_queue.is_empty(cs);
    // we can only skip the full circuit if we are not in any form of progress
    let can_finish_immediatelly =
        Boolean::multi_and(cs, &[state.read_precompile_call, input_queue_is_empty]);

    if crate::config::CIRCUIT_VERSOBE {
        dbg!(can_finish_immediatelly.witness_hook(cs)());
        dbg!(state.witness_hook(cs)());
    }

    state.read_precompile_call = state
        .read_precompile_call
        .mask_negated(cs, can_finish_immediatelly);
    state.read_words_for_round = state
        .read_words_for_round
        .mask_negated(cs, can_finish_immediatelly);
    state.completed = Boolean::multi_or(cs, &[state.completed, can_finish_immediatelly]);

    if crate::config::CIRCUIT_VERSOBE {
        dbg!(state.witness_hook(cs)());
        dbg!(precompile_calls_queue.into_state().witness_hook(cs)());
        memory_read_witness.print_debug_info();
    }

    // main work cycle
    for _cycle in 0..limit {
        if crate::config::CIRCUIT_VERSOBE {
            dbg!(_cycle);
            dbg!(state.witness_hook(cs)());
            dbg!(precompile_calls_queue.into_state().witness_hook(cs)());
        }
        // if we are in a proper state then get the ABI from the queue
        let (precompile_call, _) = precompile_calls_queue.pop_front(cs, state.read_precompile_call);

        Num::conditionally_enforce_equal(
            cs,
            state.read_precompile_call,
            &Num::from_variable(precompile_call.aux_byte.get_variable()),
            &Num::from_variable(aux_byte_for_precompile.get_variable()),
        );
        for (a, b) in precompile_call
            .address
            .inner
            .iter()
            .zip(precompile_address.inner.iter())
        {
            Num::conditionally_enforce_equal(
                cs,
                state.read_precompile_call,
                &Num::from_variable(a.get_variable()),
                &Num::from_variable(b.get_variable()),
            );
        }

        // now compute some parameters that describe the call itself

        let params_encoding = precompile_call.key;
        let call_params = EcPairingPrecompileCallParams::from_encoding(cs, params_encoding);

        state.precompile_call_params = EcPairingPrecompileCallParams::conditionally_select(
            cs,
            state.read_precompile_call,
            &call_params,
            &state.precompile_call_params,
        );
        // also set timestamps
        state.timestamp_to_use_for_read = UInt32::conditionally_select(
            cs,
            state.read_precompile_call,
            &precompile_call.timestamp,
            &state.timestamp_to_use_for_read,
        );

        // timestamps have large space, so this can be expected
        let timestamp_to_use_for_write =
            unsafe { state.timestamp_to_use_for_read.increment_unchecked(cs) };
        state.timestamp_to_use_for_write = UInt32::conditionally_select(
            cs,
            state.read_precompile_call,
            &timestamp_to_use_for_write,
            &state.timestamp_to_use_for_write,
        );

        let _reset_buffer = Boolean::multi_or(cs, &[state.read_precompile_call, state.completed]);
        state.read_words_for_round = Boolean::multi_or(
            cs,
            &[state.read_precompile_call, state.read_words_for_round],
        );
        state.read_precompile_call = boolean_false;

        let zero_pairs_left = state.precompile_call_params.num_pairs.is_zero(cs);

        let mut read_values = [zero_u256; NUM_MEMORY_READS_PER_CYCLE];
        let should_read = zero_pairs_left.negated(cs);
        let mut bias_variable = should_read.get_variable();
        for dst in read_values.iter_mut() {
            let read_query_value =
                memory_read_witness.conditionally_allocate_biased(cs, should_read, bias_variable);
            bias_variable = read_query_value.inner[0].get_variable();

            *dst = read_query_value;

            let read_query = MemoryQuery {
                timestamp: state.timestamp_to_use_for_read,
                memory_page: state.precompile_call_params.input_page,
                index: state.precompile_call_params.input_offset,
                rw_flag: boolean_false,
                is_ptr: boolean_false,
                value: read_query_value,
            };

            let may_be_new_offset = unsafe {
                state
                    .precompile_call_params
                    .input_offset
                    .increment_unchecked(cs)
            };
            state.precompile_call_params.input_offset = UInt32::conditionally_select(
                cs,
                state.read_words_for_round,
                &may_be_new_offset,
                &state.precompile_call_params.input_offset,
            );

            // perform read
            memory_queue.push(cs, read_query, should_read);
        }

        let may_be_new_num_pairs = unsafe {
            state
                .precompile_call_params
                .num_pairs
                .decrement_unchecked(cs)
        };
        state.precompile_call_params.num_pairs = UInt32::conditionally_select(
            cs,
            state.read_words_for_round,
            &may_be_new_num_pairs,
            &state.precompile_call_params.num_pairs,
        );

        let [mut p_x, mut p_y, mut q_x_c1, mut q_x_c0, mut q_y_c1, mut q_y_c0] = read_values;

        let (success, mut result) = pair(
            cs,
            &mut p_x,
            &mut p_y,
            &mut q_x_c0,
            &mut q_x_c1,
            &mut q_y_c0,
            &mut q_y_c1,
        );

        let mut acc = result.mul(cs, &mut state.pairing_inner_state.clone());
        state.pairing_inner_state = <Fq12<
            _,
            BN256Fq,
            NonNativeFieldOverU16<_, bn256::Fq, 17>,
            BN256Extension12Params,
        > as NonNativeField<F, BN256Fq>>::conditionally_select(
            cs,
            state.read_words_for_round,
            &acc,
            &state.pairing_inner_state,
        );

        let no_pairs_left = state.precompile_call_params.num_pairs.is_zero(cs);
        let write_result = Boolean::multi_and(cs, &[state.read_words_for_round, no_pairs_left]);

        let success_as_u32 = unsafe { UInt32::from_variable_unchecked(success.get_variable()) };
        let mut success = zero_u256;
        success.inner[0] = success_as_u32;

        let success_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: state.precompile_call_params.output_page,
            index: state.precompile_call_params.output_offset,
            rw_flag: boolean_true,
            is_ptr: boolean_false,
            value: success,
        };

        let _ = memory_queue.push(cs, success_query, write_result);

        state.precompile_call_params.output_offset = unsafe {
            state
                .precompile_call_params
                .output_offset
                .increment_unchecked(cs)
        };

        let paired = acc.sub(cs, &mut one_fq12.clone()).is_zero(cs);
        let paired_as_u32 = unsafe { UInt32::from_variable_unchecked(paired.get_variable()) };
        let mut paired = zero_u256;
        paired.inner[0] = paired_as_u32;

        let write_query = MemoryQuery {
            timestamp: state.timestamp_to_use_for_write,
            memory_page: state.precompile_call_params.output_page,
            index: state.precompile_call_params.output_offset,
            rw_flag: boolean_true,
            is_ptr: boolean_false,
            value: paired,
        };

        memory_queue.push(cs, write_query, write_result);

        let input_is_empty = precompile_calls_queue.is_empty(cs);
        let input_is_not_empty = input_is_empty.negated(cs);
        let nothing_left = Boolean::multi_and(cs, &[write_result, input_is_empty]);
        let process_next = Boolean::multi_and(cs, &[write_result, input_is_not_empty]);

        state.read_precompile_call = process_next;
        state.completed = Boolean::multi_or(cs, &[nothing_left, state.completed]);
        let t = Boolean::multi_or(cs, &[state.read_precompile_call, state.completed]);
        state.read_words_for_round = t.negated(cs);

        if crate::config::CIRCUIT_VERSOBE {
            dbg!(state.witness_hook(cs)());
            dbg!(precompile_calls_queue.into_state().witness_hook(cs)());
        }
    }

    if crate::config::CIRCUIT_VERSOBE {
        dbg!(state.witness_hook(cs)());
        dbg!(precompile_calls_queue.into_state().witness_hook(cs)());
    }

    precompile_calls_queue.enforce_consistency(cs);

    state
}

pub fn ecpairing_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: EcPairingCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    let EcPairingCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;

    let mut structured_input =
        EcPairingCircuitInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());

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

    let mut starting_fsm_state = EcPairingFunctionFSM::placeholder(cs);
    starting_fsm_state.read_precompile_call = Boolean::allocated_constant(cs, true);

    let initial_state = EcPairingFunctionFSM::conditionally_select(
        cs,
        start_flag,
        &starting_fsm_state,
        &structured_input.hidden_fsm_input.internal_fsm,
    );

    let final_state = ecpairing_precompile_inner::<F, CS, R>(
        cs,
        &mut memory_queue,
        &mut requests_queue,
        read_queries_allocator,
        initial_state,
        round_function,
        limit,
    );

    let final_memory_state = memory_queue.into_state();
    let final_requests_state = requests_queue.into_state();

    let done = final_state.completed;
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::placeholder(cs);

    structured_input.observable_output.final_memory_state = QueueState::conditionally_select(
        cs,
        structured_input.completion_flag,
        &final_memory_state,
        &structured_input.observable_output.final_memory_state,
    );

    structured_input.hidden_fsm_output.internal_fsm = final_state;
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
