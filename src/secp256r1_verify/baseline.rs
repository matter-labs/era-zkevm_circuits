use super::*;

use crate::base_structures::precompile_input_outputs::PrecompileFunctionOutputData;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;

use arrayvec::ArrayVec;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::curves::sw_projective::SWProjectivePoint;

use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;

use boojum::gadgets::u160::UInt160;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;

use std::collections::VecDeque;
use std::sync::{Arc, RwLock};
use zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE;

use crate::ecrecover::baseline::convert_uint256_to_field_element;
use crate::ecrecover::baseline::convert_uint256_to_field_element_masked;
use crate::ecrecover::new_optimized::fixed_base_mul;

const WINDOW_WIDTH: usize = 4;
const NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4: usize = 64;
const PRECOMPUTATION_TABLE_SIZE: usize = (1 << WINDOW_WIDTH) - 1;

#[derive(Derivative, CSSelectable)]
#[derivative(Clone, Debug)]
pub struct Secp256r1VerifyPrecompileCallParams<F: SmallField> {
    pub input_page: UInt32<F>,
    pub input_offset: UInt32<F>,
    pub output_page: UInt32<F>,
    pub output_offset: UInt32<F>,
}

impl<F: SmallField> Secp256r1VerifyPrecompileCallParams<F> {
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

const NUM_WORDS: usize = 17;
const EXCEPTION_FLAGS_ARR_LEN: usize = 8;

fn secp256r1_verify_function_inner<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    r: &UInt256<F>,
    s: &UInt256<F>,
    message_hash: &UInt256<F>,
    x: &UInt256<F>,
    y: &UInt256<F>,
    base_field_params: &Arc<Secp256BaseNNFieldParams>,
    scalar_field_params: &Arc<Secp256ScalarNNFieldParams>,
) -> (Boolean<F>, UInt256<F>) {
    use boojum::pairing::GenericCurveAffine;
    let curve_a = Secp256Affine::a_coeff();
    let curve_b = Secp256Affine::b_coeff();

    let mut curve_a_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, curve_a, &base_field_params);
    let mut curve_b_nn =
        Secp256BaseNNField::<F>::allocated_constant(cs, curve_b, &base_field_params);

    let generator = Secp256Affine::one();
    let (gen_x, gen_y) = generator.into_xy_unchecked();
    let gen_x_nn = Secp256BaseNNField::allocated_constant(cs, gen_x, base_field_params);
    let gen_y_nn = Secp256BaseNNField::allocated_constant(cs, gen_y, base_field_params);

    let secp_n_u256 = U256([
        scalar_field_params.modulus_u1024.as_ref().as_words()[0],
        scalar_field_params.modulus_u1024.as_ref().as_words()[1],
        scalar_field_params.modulus_u1024.as_ref().as_words()[2],
        scalar_field_params.modulus_u1024.as_ref().as_words()[3],
    ]);
    let secp_n_u256 = UInt256::allocated_constant(cs, secp_n_u256);

    let secp_p_u256 = U256([
        base_field_params.modulus_u1024.as_ref().as_words()[0],
        base_field_params.modulus_u1024.as_ref().as_words()[1],
        base_field_params.modulus_u1024.as_ref().as_words()[2],
        base_field_params.modulus_u1024.as_ref().as_words()[3],
    ]);
    let secp_p_u256 = UInt256::allocated_constant(cs, secp_p_u256);

    let mut exception_flags = ArrayVec::<_, EXCEPTION_FLAGS_ARR_LEN>::new();

    // we use non-compressed point, so we:
    // - check that public key is on curve (no special handling of zeroes)
    // - check verification equation

    // we check ranges upfront. We only need to check <modulus, and conversion functions will perform masking internally for values that are >= 1

    let mut r_as_u256 = *r;
    let mut s_as_u256 = *s;
    let mut x_as_u256 = *x;
    let mut y_as_u256 = *y;

    let (_res, is_in_range) = r_as_u256.overflowing_sub(cs, &secp_n_u256);
    r_as_u256 = r_as_u256.mask(cs, is_in_range);
    let r_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(r_is_not_in_range);

    let (_res, is_in_range) = s_as_u256.overflowing_sub(cs, &secp_n_u256);
    s_as_u256 = s_as_u256.mask(cs, is_in_range);
    let s_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(s_is_not_in_range);

    let (_res, is_in_range) = x_as_u256.overflowing_sub(cs, &secp_p_u256);
    x_as_u256 = x_as_u256.mask(cs, is_in_range);
    let x_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(x_is_not_in_range);

    let (_res, is_in_range) = y_as_u256.overflowing_sub(cs, &secp_p_u256);
    y_as_u256 = y_as_u256.mask(cs, is_in_range);
    let y_is_not_in_range = is_in_range.negated(cs);
    exception_flags.push(y_is_not_in_range);

    let mut x_fe = convert_uint256_to_field_element(cs, &x_as_u256, &base_field_params);
    let mut y_fe = convert_uint256_to_field_element(cs, &y_as_u256, &base_field_params);

    let (mut r_fe, r_is_zero) =
        convert_uint256_to_field_element_masked(cs, &r_as_u256, &scalar_field_params);
    exception_flags.push(r_is_zero);
    let (mut s_fe, s_is_zero) =
        convert_uint256_to_field_element_masked(cs, &s_as_u256, &scalar_field_params);
    exception_flags.push(s_is_zero);

    let mut message_hash_fe =
        convert_uint256_to_field_element(cs, &message_hash, &scalar_field_params);

    // perform on-curve check
    let mut lhs = y_fe.clone();
    let mut lhs = lhs.mul(cs, &mut y_fe);
    lhs.normalize(cs);

    let mut rhs = x_fe.clone();
    let mut rhs = rhs.mul(cs, &mut x_fe);
    let mut rhs = rhs.add(cs, &mut curve_a_nn);
    let mut rhs = rhs.mul(cs, &mut x_fe);
    let mut rhs = rhs.add(cs, &mut curve_b_nn);
    rhs.normalize(cs);

    let is_on_curve = NonNativeFieldOverU16::equals(cs, &mut lhs, &mut rhs);
    let not_on_curve = is_on_curve.negated(cs);
    exception_flags.push(not_on_curve);

    // we can mask point to ensure that our arithmetic formulas work
    let x_fe: NonNativeFieldOverU16<F, Secp256Fq, 17> =
        NonNativeFieldOverU16::conditionally_select(cs, is_on_curve, &x_fe, &gen_x_nn);
    let y_fe = NonNativeFieldOverU16::conditionally_select(cs, is_on_curve, &y_fe, &gen_y_nn);

    // this always exists (0 was an exception and was masked)
    let mut s_fe_inversed = s_fe.inverse_unchecked(cs);
    let mut r_by_s_inv = r_fe.mul(cs, &mut s_fe_inversed);
    let mut message_hash_by_s_inv = message_hash_fe.mul(cs, &mut s_fe_inversed);

    r_by_s_inv.normalize(cs);
    message_hash_by_s_inv.normalize(cs);

    // now we do multiplication
    // it's safe since we checked not-on-curve above
    let point = SWProjectivePoint::<F, Secp256Affine, Secp256BaseNNField<F>>::from_xy_unchecked(
        cs, x_fe, y_fe,
    );
    let mut r_by_s_inv_mul_by_pubkey =
        width_4_windowed_multiplication(cs, point, r_by_s_inv.clone(), &base_field_params);

    let mut full_table_ids = vec![];
    seq_macro::seq!(C in 0..32 {
        let ids = [
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<0, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<1, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<2, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<3, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<4, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<5, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<6, C>>()
                .expect("table must exist"),
            cs.get_table_id_for_marker::<Secp256r1FixedBaseMulTable<7, C>>()
                .expect("table must exist"),
        ];
        full_table_ids.push(ids);
    });

    let mut hash_times_g = fixed_base_mul::<F, CS, Secp256Fr, Secp256Fq, Secp256Affine, 17>(
        cs,
        message_hash_by_s_inv,
        &base_field_params,
        SCALAR_FIELD_CANONICAL_REPR_LIMBS,
        BASE_FIELD_CANONICAL_REPR_LIMBS,
        &full_table_ids,
    );

    let (mut q_acc, is_infinity) =
        hash_times_g.convert_to_affine_or_default(cs, Secp256Affine::one());
    let q_acc_added = r_by_s_inv_mul_by_pubkey.add_mixed(cs, &mut q_acc);
    let mut q_acc =
        Selectable::conditionally_select(cs, is_infinity, &r_by_s_inv_mul_by_pubkey, &q_acc_added);

    let ((mut q_x, _q_y), is_infinity) =
        q_acc.convert_to_affine_or_default(cs, Secp256Affine::one());
    exception_flags.push(is_infinity);
    let any_exception = Boolean::multi_or(cs, &exception_flags[..]);

    q_x.normalize(cs);

    // now compare mod n. For that we go out of limbs and back
    let limbs = q_x.limbs;
    let mut q_x_mod_n = NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 2 }, // |Fr|*2 < |Fq|
        form: RepresentationForm::Normalized,
        params: scalar_field_params.clone(),
        _marker: std::marker::PhantomData,
    };
    q_x_mod_n.normalize(cs);

    let signature_equality = NonNativeFieldOverU16::equals(cs, &mut q_x_mod_n, &mut r_fe);
    let written_value_bool = signature_equality.mask_negated(cs, any_exception);
    let all_ok = any_exception.negated(cs);

    let mut written_value = UInt256::zero(cs);
    written_value.inner[0] =
        unsafe { UInt32::from_variable_unchecked(written_value_bool.get_variable()) };

    (all_ok, written_value)
}

pub fn secp256r1_verify_function_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: Secp256r1VerifyCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <MemoryQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    assert!(limit <= u32::MAX as usize);

    let Secp256r1VerifyCircuitInstanceWitness {
        closed_form_input,
        requests_queue_witness,
        memory_reads_witness,
    } = witness;

    let memory_reads_witness: VecDeque<_> = memory_reads_witness.into_iter().flatten().collect();

    let precompile_address = UInt160::allocated_constant(
        cs,
        *zkevm_opcode_defs::system_params::SECP256R1_VERIFY_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS,
    );
    let aux_byte_for_precompile = UInt8::allocated_constant(cs, PRECOMPILE_AUX_BYTE);

    let scalar_params = Arc::new(secp256r1_scalar_field_params());
    let base_params = Arc::new(secp256r1_base_field_params());

    let mut structured_input =
        Secp256r1VerifyCircuitInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());
    let start_flag = structured_input.start_flag;

    let requests_queue_state_from_input = structured_input.observable_input.initial_log_queue_state;

    // it must be trivial
    requests_queue_state_from_input.enforce_trivial_head(cs);

    let requests_queue_state_from_fsm = structured_input.hidden_fsm_input.log_queue_state;

    let requests_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &requests_queue_state_from_input,
        &requests_queue_state_from_fsm,
    );

    let memory_queue_state_from_input =
        structured_input.observable_input.initial_memory_queue_state;

    // it must be trivial
    memory_queue_state_from_input.enforce_trivial_head(cs);

    let memory_queue_state_from_fsm = structured_input.hidden_fsm_input.memory_queue_state;

    let memory_queue_state = QueueState::conditionally_select(
        cs,
        start_flag,
        &memory_queue_state_from_input,
        &memory_queue_state_from_fsm,
    );

    let mut requests_queue = StorageLogQueue::<F, R>::from_state(cs, requests_queue_state);
    let queue_witness = CircuitQueueWitness::from_inner_witness(requests_queue_witness);
    requests_queue.witness = Arc::new(queue_witness);

    let mut memory_queue = MemoryQueue::<F, R>::from_state(cs, memory_queue_state);

    let one_u32 = UInt32::allocated_constant(cs, 1u32);
    let zero_u256 = UInt256::zero(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);

    use crate::storage_application::ConditionalWitnessAllocator;
    let read_queries_allocator = ConditionalWitnessAllocator::<F, UInt256<F>> {
        witness_source: Arc::new(RwLock::new(memory_reads_witness)),
    };

    for _cycle in 0..limit {
        let is_empty = requests_queue.is_empty(cs);
        let should_process = is_empty.negated(cs);
        let (request, _) = requests_queue.pop_front(cs, should_process);

        let mut precompile_call_params =
            Secp256r1VerifyPrecompileCallParams::from_encoding(cs, request.key);

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

        let mut read_values = [zero_u256; MEMORY_QUERIES_PER_CALL];
        let mut bias_variable = should_process.get_variable();
        for dst in read_values.iter_mut() {
            let read_query_value: UInt256<F> = read_queries_allocator
                .conditionally_allocate_biased(cs, should_process, bias_variable);
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

        let [message_hash_as_u256, r_as_u256, s_as_u256, x_as_u256, y_as_u256] = read_values;

        let (success, written_value) = secp256r1_verify_function_inner(
            cs,
            &r_as_u256,
            &s_as_u256,
            &message_hash_as_u256,
            &x_as_u256,
            &y_as_u256,
            &base_params,
            &scalar_params,
        );

        let success_as_u32 = unsafe { UInt32::from_variable_unchecked(success.get_variable()) };
        let mut success_as_u256 = zero_u256;
        success_as_u256.inner[0] = success_as_u32;

        let success_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            index: precompile_call_params.output_offset,
            rw_flag: boolean_true,
            value: success_as_u256,
            is_ptr: boolean_false,
        };

        precompile_call_params.output_offset = precompile_call_params
            .output_offset
            .add_no_overflow(cs, one_u32);

        let _ = memory_queue.push(cs, success_query, should_process);

        let value_query = MemoryQuery {
            timestamp: timestamp_to_use_for_write,
            memory_page: precompile_call_params.output_page,
            index: precompile_call_params.output_offset,
            rw_flag: boolean_true,
            value: written_value,
            is_ptr: boolean_false,
        };

        let _ = memory_queue.push(cs, value_query, should_process);
    }

    requests_queue.enforce_consistency(cs);

    // form the final state
    let done = requests_queue.is_empty(cs);
    structured_input.completion_flag = done;
    structured_input.observable_output = PrecompileFunctionOutputData::placeholder(cs);

    let final_memory_state = memory_queue.into_state();
    let final_requets_state = requests_queue.into_state();

    structured_input.observable_output.final_memory_state = QueueState::conditionally_select(
        cs,
        structured_input.completion_flag,
        &final_memory_state,
        &structured_input.observable_output.final_memory_state,
    );

    structured_input.hidden_fsm_output.log_queue_state = final_requets_state;
    structured_input.hidden_fsm_output.memory_queue_state = final_memory_state;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    use boojum::cs::gates::PublicInputGate;

    let compact_form =
        ClosedFormInputCompactForm::from_full_form(cs, &structured_input, round_function);
    let input_commitment = commit_variable_length_encodable_item(cs, &compact_form, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}

fn width_4_windowed_multiplication<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut point: SWProjectivePoint<F, Secp256Affine, Secp256BaseNNField<F>>,
    mut scalar: Secp256ScalarNNField<F>,
    base_field_params: &Arc<Secp256BaseNNFieldParams>,
) -> SWProjectivePoint<F, Secp256Affine, Secp256BaseNNField<F>> {
    scalar.enforce_reduced(cs);

    use boojum::pairing::GenericCurveAffine;

    // create precomputed table of size 1<<4 - 1
    // there is no 0 * P in the table, we will handle it below
    let mut table = Vec::with_capacity(PRECOMPUTATION_TABLE_SIZE);
    let mut tmp = point.clone();
    let (mut p_affine, _) = point.convert_to_affine_or_default(cs, Secp256Affine::one());
    table.push(p_affine.clone());
    for _ in 1..PRECOMPUTATION_TABLE_SIZE {
        // 2P, 3P, ...
        tmp = tmp.add_mixed(cs, &mut p_affine);
        let (affine, _) = tmp.convert_to_affine_or_default(cs, Secp256Affine::one());
        table.push(affine);
    }
    assert_eq!(table.len(), PRECOMPUTATION_TABLE_SIZE);

    // now decompose every scalar we are interested in
    let msb_decomposition = to_width_4_window_form(cs, scalar);

    let mut comparison_constants = Vec::with_capacity(PRECOMPUTATION_TABLE_SIZE);
    for i in 1..=PRECOMPUTATION_TABLE_SIZE {
        let constant = Num::allocated_constant(cs, F::from_u64_unchecked(i as u64));
        comparison_constants.push(constant);
    }

    // now we just do double and add
    let mut acc = SWProjectivePoint::zero(cs, base_field_params);
    assert_eq!(
        msb_decomposition.len(),
        NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4
    );

    for (idx, window_idx) in msb_decomposition.into_iter().enumerate() {
        let ignore_part = window_idx.is_zero(cs);

        let (mut selected_part_x, mut selected_part_y) = table[0].clone();
        for i in 1..PRECOMPUTATION_TABLE_SIZE {
            let should_select = Num::equals(cs, &comparison_constants[i], &window_idx);
            selected_part_x =
                Selectable::conditionally_select(cs, should_select, &table[i].0, &selected_part_x);
            selected_part_y =
                Selectable::conditionally_select(cs, should_select, &table[i].1, &selected_part_y);
        }

        let tmp_acc = acc.add_mixed(cs, &mut (selected_part_x, selected_part_y));
        acc = Selectable::conditionally_select(cs, ignore_part, &acc, &tmp_acc);

        if idx != NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4 - 1 {
            for _ in 0..WINDOW_WIDTH {
                acc = acc.double(cs);
            }
        }
    }

    acc
}

fn to_width_4_window_form<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut limited_width_scalar: Secp256ScalarNNField<F>,
) -> Vec<Num<F>> {
    limited_width_scalar.enforce_reduced(cs);
    // we know that width is 128 bits, so just do BE decomposition and put into resulting array
    let zero_num = Num::zero(cs);
    for word in limited_width_scalar.limbs[16..].iter() {
        let word = Num::from_variable(*word);
        Num::enforce_equal(cs, &word, &zero_num);
    }

    use boojum::gadgets::tables::ByteSplitTable;
    use boojum::gadgets::u16::UInt16;
    let byte_split_id = cs
        .get_table_id_for_marker::<ByteSplitTable<4>>()
        .expect("table should exist");
    let mut result = Vec::with_capacity(NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4);
    for word in limited_width_scalar.limbs[..16].iter().rev() {
        let word = unsafe { UInt16::from_variable_unchecked(*word) };
        let [high, low] = word.to_be_bytes(cs);
        for t in [high, low].into_iter() {
            let [l, h] = cs.perform_lookup::<1, 2>(byte_split_id, &[t.get_variable()]);
            let h = Num::from_variable(h);
            let l = Num::from_variable(l);
            result.push(h);
            result.push(l);
        }
    }
    assert_eq!(result.len(), NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4);

    result
}

#[cfg(test)]
mod test {
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::traits::allocatable::CSAllocatable;
    use boojum::worker::Worker;

    use super::*;

    type F = GoldilocksField;
    type P = GoldilocksField;

    use boojum::config::DevCSConfig;

    use boojum::cs::cs_builder::*;
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::*;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::CSGeometry;
    use boojum::cs::*;
    use boojum::gadgets::tables::*;

    #[test]
    fn test_secp256r1_verification() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 8,
        };

        let max_variables = 1 << 26;
        let max_trace_len = 1 << 20;

        fn configure<
            F: SmallField,
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: 16,
                    share_table_id: true,
                },
            );

            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = BooleanConstraintGate::configure_builder(
                builder,
                GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions: 1,
                    share_constants: false,
                },
            );
            let builder = U8x4FMAGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<32>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<16>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<8>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = DotProductGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = SelectionGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ParallelSelectionGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = PublicInputGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<_, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(max_variables);

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        seq_macro::seq!(C in 0..32 {
            let table = create_secp256r1_fixed_base_mul_table::<F, 0, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<0, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 1, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<1, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 2, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<2, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 3, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<3, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 4, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<4, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 5, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<5, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 6, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<6, C>, 3>(table);
            let table = create_secp256r1_fixed_base_mul_table::<F, 7, C>();
            owned_cs.add_lookup_table::<Secp256r1FixedBaseMulTable<7, C>, 3>(table);
        });

        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let cs = &mut owned_cs;

        let digest =
            hex::decode("3fec5769b5cf4e310a7d150508e82fb8e3eda1c2c94c61492d3bd8aea99e06c9")
                .unwrap();
        let pk_x = hex::decode("31a80482dadf89de6302b1988c82c29544c9c07bb910596158f6062517eb089a")
            .unwrap();
        let pk_y = hex::decode("2f54c9a0f348752950094d3228d3b940258c75fe2a413cb70baa21dc2e352fc5")
            .unwrap();
        let r = hex::decode("e22466e928fdccef0de49e3503d2657d00494a00e764fd437bdafa05f5922b1f")
            .unwrap();
        let s = hex::decode("bbb77c6817ccf50748419477e843d5bac67e6a70e97dde5a57e0c983b777e1ad")
            .unwrap();

        let scalar_params = secp256r1_scalar_field_params();
        let base_params = secp256r1_base_field_params();

        let digest_u256 = U256::from_big_endian(&digest);
        let pk_x_u256 = U256::from_big_endian(&pk_x);
        let pk_y_u256 = U256::from_big_endian(&pk_y);
        let r_u256 = U256::from_big_endian(&r);
        let s_u256 = U256::from_big_endian(&s);

        let pk_x = UInt256::allocate(cs, pk_x_u256);
        let pk_y = UInt256::allocate(cs, pk_y_u256);
        let r = UInt256::allocate(cs, r_u256);
        let s = UInt256::allocate(cs, s_u256);
        let digest = UInt256::allocate(cs, digest_u256);

        let scalar_params = Arc::new(scalar_params);
        let base_params = Arc::new(base_params);

        let (no_error, is_valid) = secp256r1_verify_function_inner(
            cs,
            &r,
            &s,
            &digest,
            &pk_x,
            &pk_y,
            &base_params,
            &scalar_params,
        );

        assert!(no_error.witness_hook(&*cs)().unwrap() == true);
        assert!(is_valid.witness_hook(&*cs)().unwrap() == U256::one());

        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
