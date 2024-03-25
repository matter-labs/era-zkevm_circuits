use boojum::gadgets::u256::UInt256;

use crate::{
    base_structures::{
        log_query::{self, LogQuery, LOG_QUERY_PACKED_WIDTH, ROLLBACK_PACKING_FLAG_VARIABLE_IDX},
        register::VMRegister,
    },
    main_vm::opcodes::call_ret_impl::add_to_decommittment_queue_inner,
    tables::{test_bit::TestBitTable, PubdataCostValidityTable},
};

use super::*;
use crate::base_structures::decommit_query::DecommitQueryWitness;
use crate::main_vm::opcodes::log::log_query::LogQueryWitness;
use crate::main_vm::witness_oracle::SynchronizedWitnessOracle;
use crate::main_vm::witness_oracle::WitnessOracle;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::gadgets::traits::allocatable::CSAllocatableExt;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;

pub(crate) fn test_if_bit_is_set<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    byte: &UInt8<F>,
    bit: u32,
) -> Boolean<F> {
    debug_assert!(bit < 8);
    let bit_idx_as_variable = UInt8::allocated_constant(cs, bit as u8);
    let table_id = cs
        .get_table_id_for_marker::<TestBitTable>()
        .expect("table for bit tests must exist");
    let res = cs.perform_lookup::<2, 1>(
        table_id,
        &[byte.get_variable(), bit_idx_as_variable.get_variable()],
    );
    let res = unsafe { Boolean::from_variable_unchecked(res[0]) };

    res
}

pub(crate) fn i32_add_no_overflow<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &UInt32<F>,
    b: &UInt32<F>,
) -> UInt32<F> {
    // condition for overflow is if we add two number >0 and get one <0 (by highest bit),
    // or add two <0 and get one >0

    let a_bytes = a.to_le_bytes(cs);
    let a_is_negative = test_if_bit_is_set(cs, &a_bytes[3], 7);
    let b_bytes = b.to_le_bytes(cs);
    let b_is_negative = test_if_bit_is_set(cs, &b_bytes[3], 7);
    let (result, _of) = a.overflowing_add(cs, *b);
    let result_bytes = result.to_le_bytes(cs);
    let result_is_negative = test_if_bit_is_set(cs, &result_bytes[3], 7);

    let a_is_positive = a_is_negative.negated(cs);
    let b_is_positive = b_is_negative.negated(cs);
    let result_is_positive = result_is_negative.negated(cs);

    let of_0 = Boolean::multi_and(cs, &[a_is_positive, b_is_positive, result_is_negative]);
    let of_1 = Boolean::multi_and(cs, &[a_is_negative, b_is_negative, result_is_positive]);
    let of = Boolean::multi_or(cs, &[of_0, of_1]);
    let boolean_false = Boolean::allocated_constant(cs, false);
    Boolean::enforce_equal(cs, &of, &boolean_false);

    result
}

pub(crate) fn i32_sub_no_underflow<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &UInt32<F>,
    b: &UInt32<F>,
) -> UInt32<F> {
    // exception is when a > 0, b < 0, and result is <0,
    // or if a < 0, b > 0, and result >0
    let a_bytes = a.to_le_bytes(cs);
    let a_is_negative = test_if_bit_is_set(cs, &a_bytes[3], 7);
    let b_bytes = b.to_le_bytes(cs);
    let b_is_negative = test_if_bit_is_set(cs, &b_bytes[3], 7);
    let (result, _of) = a.overflowing_sub(cs, *b);
    let result_bytes = result.to_le_bytes(cs);
    let result_is_negative = test_if_bit_is_set(cs, &result_bytes[3], 7);

    let a_is_positive = a_is_negative.negated(cs);
    let b_is_positive = b_is_negative.negated(cs);
    let result_is_positive = result_is_negative.negated(cs);

    let of_0 = Boolean::multi_and(cs, &[a_is_positive, b_is_negative, result_is_negative]);
    let of_1 = Boolean::multi_and(cs, &[a_is_negative, b_is_positive, result_is_positive]);
    let of = Boolean::multi_or(cs, &[of_0, of_1]);
    let boolean_false = Boolean::allocated_constant(cs, false);
    Boolean::enforce_equal(cs, &of, &boolean_false);

    result
}

pub(crate) fn normalize_bytecode_hash_for_decommit<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    bytecode_hash: &mut UInt256<F>,
) {
    let zero_u32 = UInt32::zero(cs);
    bytecode_hash.inner[7] = zero_u32;
}

pub(crate) fn apply_log<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    W: WitnessOracle<F>,
>(
    cs: &mut CS,
    draft_vm_state: &VmLocalState<F>,
    common_opcode_state: &CommonOpcodeState<F>,
    opcode_carry_parts: &AfterDecodingCarryParts<F>,
    diffs_accumulator: &mut StateDiffsAccumulator<F>,
    witness_oracle: &SynchronizedWitnessOracle<F, W>,
    round_function: &R,
) where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    const STORAGE_READ_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::StorageRead);
    const STORAGE_WRITE_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::StorageWrite);
    const L1_MESSAGE_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::ToL1Message);
    const EVENT_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::Event);
    const PRECOMPILE_CALL_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::PrecompileCall);
    const DECOMMIT_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::Decommit);
    const TRANSIENT_STORAGE_READ_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::TransientStorageRead);
    const TRANSIENT_STORAGE_WRITE_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Log(LogOpcode::TransientStorageWrite);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(STORAGE_READ_OPCODE);

    let is_storage_read = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(STORAGE_READ_OPCODE)
    };
    let is_storage_write = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(STORAGE_WRITE_OPCODE)
    };
    let is_event = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(EVENT_OPCODE)
    };
    let is_l1_message = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(L1_MESSAGE_OPCODE)
    };
    let is_precompile = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(PRECOMPILE_CALL_OPCODE)
    };
    let is_decommit = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(DECOMMIT_OPCODE)
    };
    let is_transient_storage_read = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(TRANSIENT_STORAGE_READ_OPCODE)
    };
    let is_transient_storage_write = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .boolean_for_variant(TRANSIENT_STORAGE_WRITE_OPCODE)
    };

    if crate::config::CIRCUIT_VERSOBE {
        if should_apply.witness_hook(&*cs)().unwrap_or(false) {
            println!("Applying LOG");
            if is_storage_read.witness_hook(&*cs)().unwrap_or(false) {
                println!("SLOAD");
            }
            if is_storage_write.witness_hook(&*cs)().unwrap_or(false) {
                println!("SSTORE");
            }
            if is_event.witness_hook(&*cs)().unwrap_or(false) {
                println!("EVENT");
            }
            if is_l1_message.witness_hook(&*cs)().unwrap_or(false) {
                println!("L2 to L1 message");
            }
            if is_precompile.witness_hook(&*cs)().unwrap_or(false) {
                println!("PRECOMPILECALL");
            }
            if is_decommit.witness_hook(&*cs)().unwrap_or(false) {
                println!("DECOMMIT");
            }
            if is_transient_storage_read.witness_hook(&*cs)().unwrap_or(false) {
                println!("TLOAD");
            }
            if is_transient_storage_write.witness_hook(&*cs)().unwrap_or(false) {
                println!("TSTORE");
            }
        }
    }

    let address = draft_vm_state.callstack.current_context.saved_context.this;

    let mut key = UInt256 {
        inner: common_opcode_state.src0_view.u32x8_view,
    };
    let written_value = UInt256 {
        inner: common_opcode_state.src1_view.u32x8_view,
    };

    // modify the key by replacing parts for precompile call
    let read_page_is_zero = key.inner[4].is_zero(cs);
    let write_page_is_zero = key.inner[5].is_zero(cs);
    let precompile_memory_page_to_read = opcode_carry_parts.heap_page;
    let precompile_memory_page_to_write = opcode_carry_parts.heap_page;
    let should_swap_read_page = Boolean::multi_and(cs, &[read_page_is_zero, is_precompile]);
    let should_swap_write_page = Boolean::multi_and(cs, &[write_page_is_zero, is_precompile]);
    // replace bits 128..160 and 160..192
    key.inner[4] = UInt32::conditionally_select(
        cs,
        should_swap_read_page,
        &precompile_memory_page_to_read,
        &key.inner[4],
    );
    key.inner[5] = UInt32::conditionally_select(
        cs,
        should_swap_write_page,
        &precompile_memory_page_to_write,
        &key.inner[5],
    );

    let precompile_call_ergs_cost = common_opcode_state.src1_view.u32x8_view[0];
    let precompile_call_pubdata_cost = common_opcode_state.src1_view.u32x8_view[1];
    // check inplace that pubdata cost is signed, but >0

    // check that refund is >=0
    let top_byte = common_opcode_state.src1_view.u8x32_view[7];
    let is_negative = test_if_bit_is_set(cs, &top_byte, 7);
    let should_enforce = Boolean::multi_and(cs, &[is_precompile, should_apply]);
    is_negative.conditionally_enforce_false(cs, should_enforce);

    let is_state_storage_access: Boolean<F> =
        Boolean::multi_or(cs, &[is_storage_read, is_storage_write]);
    let is_io_read_like = Boolean::multi_or(cs, &[is_storage_read, is_transient_storage_read]);
    let is_io_write_like = Boolean::multi_or(cs, &[is_storage_write, is_transient_storage_write]);
    let is_transient_storage_access =
        Boolean::multi_or(cs, &[is_transient_storage_read, is_transient_storage_write]);
    let is_storage_like_access =
        Boolean::multi_or(cs, &[is_state_storage_access, is_transient_storage_access]);
    let is_nonrevertable_io = Boolean::multi_or(cs, &[is_io_read_like, is_precompile]);
    let is_revertable_io = Boolean::multi_or(cs, &[is_io_write_like, is_event, is_l1_message]);
    let is_io_like_operation = Boolean::multi_or(cs, &[is_nonrevertable_io, is_revertable_io]);

    let aux_byte_variable = Num::linear_combination(
        cs,
        &[
            (
                is_state_storage_access.get_variable(),
                F::from_u64_unchecked(zkevm_opcode_defs::system_params::STORAGE_AUX_BYTE as u64),
            ),
            (
                is_event.get_variable(),
                F::from_u64_unchecked(zkevm_opcode_defs::system_params::EVENT_AUX_BYTE as u64),
            ),
            (
                is_l1_message.get_variable(),
                F::from_u64_unchecked(zkevm_opcode_defs::system_params::L1_MESSAGE_AUX_BYTE as u64),
            ),
            (
                is_precompile.get_variable(),
                F::from_u64_unchecked(zkevm_opcode_defs::system_params::PRECOMPILE_AUX_BYTE as u64),
            ),
            (
                is_transient_storage_access.get_variable(),
                F::from_u64_unchecked(
                    zkevm_opcode_defs::system_params::TRANSIENT_STORAGE_AUX_BYTE as u64,
                ),
            ),
        ],
    )
    .get_variable();

    let aux_byte = unsafe { UInt8::from_variable_unchecked(aux_byte_variable) };
    let timestamp = common_opcode_state.timestamp_for_first_decommit_or_precompile_read;

    let shard_id = draft_vm_state
        .callstack
        .current_context
        .saved_context
        .this_shard_id;

    // NOTE: our opcodes encoding guarantees that there is no "storage read + is first"
    // variant encodable
    let is_event_init = {
        common_opcode_state
            .decoded_opcode
            .properties_bits
            .flag_booleans[FIRST_MESSAGE_FLAG_IDX]
    };

    let zero_u256 = UInt256::zero(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);
    let tx_number = draft_vm_state.tx_number_in_block;

    // here we perform all oracle access first, and then will use values below in particular opcodes

    let mut log = LogQuery {
        address,
        key,
        read_value: zero_u256,
        written_value,
        rw_flag: is_revertable_io,
        aux_byte,
        rollback: boolean_false,
        is_service: is_event_init,
        shard_id,
        tx_number_in_block: tx_number,
        timestamp,
    };

    let oracle = witness_oracle.clone();
    let execute_storage_access = Boolean::multi_and(cs, &[should_apply, is_state_storage_access]);
    // we should assemble all the dependencies here, and we will use AllocateExt here
    let mut dependencies =
        Vec::with_capacity(<LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 2);
    dependencies.push(is_storage_write.get_variable().into());
    dependencies.push(execute_storage_access.get_variable().into());
    dependencies.extend(Place::from_variables(log.flatten_as_variables()));

    let io_pubdata_cost = UInt32::allocate_from_closure_and_dependencies(
        cs,
        move |inputs: &[F]| {
            let is_write = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[0]);
            let execute = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[1]);
            let mut log_query =
                [F::ZERO; <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            log_query.copy_from_slice(&inputs[2..]);
            let log_query: LogQueryWitness<F> =
                CSAllocatableExt::witness_from_set_of_values(log_query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            let witness = guard.get_pubdata_cost_for_query(&log_query, is_write, execute);
            drop(guard);

            witness
        },
        &dependencies,
    );
    // NOTE: it's possible to have cost negative, if it's e.g. 2nd write in a sequence of 0 -> X -> 0

    // we should nevertheless ensure that it's 0 if it's not rollup access, and not write in general
    let io_pubdata_cost = io_pubdata_cost.mask(cs, is_storage_write);
    let is_zk_rollup_access = shard_id.is_zero(cs);
    let is_zk_porter_access = is_zk_rollup_access.negated(cs);
    let io_pubdata_cost_is_zero = io_pubdata_cost.is_zero(cs);
    io_pubdata_cost_is_zero.conditionally_enforce_true(cs, is_zk_porter_access);

    // check range
    let table_id = cs
        .get_table_id_for_marker::<PubdataCostValidityTable>()
        .expect("table must exist");
    let _ = cs.perform_lookup::<1, 2>(table_id, &[io_pubdata_cost.get_variable()]);

    let oracle = witness_oracle.clone();
    let cold_warm_access_ergs_refund = UInt32::allocate_from_closure_and_dependencies(
        cs,
        move |inputs: &[F]| {
            let is_write = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[0]);
            let execute = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[1]);
            let mut log_query =
                [F::ZERO; <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            log_query.copy_from_slice(&inputs[2..]);
            let log_query: LogQueryWitness<F> =
                CSAllocatableExt::witness_from_set_of_values(log_query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            let witness = guard.get_cold_warm_refund(&log_query, is_write, execute);
            drop(guard);

            witness
        },
        &dependencies,
    );

    // we only refund storage
    let cold_warm_access_ergs_refund =
        cold_warm_access_ergs_refund.mask(cs, is_state_storage_access);

    let mut max_refund = UInt32::zero(cs);
    let sload_cost = UInt32::allocated_constant(cs, LogOpcode::StorageRead.ergs_price());
    let sstore_cost = UInt32::allocated_constant(cs, LogOpcode::StorageWrite.ergs_price());
    max_refund = UInt32::conditionally_select(cs, is_storage_read, &sload_cost, &max_refund);
    max_refund = UInt32::conditionally_select(cs, is_storage_write, &sstore_cost, &max_refund);

    let _ = max_refund.sub_no_overflow(cs, cold_warm_access_ergs_refund);

    // and also compute cost of decommit in our standard units of 32-byte words
    let versioned_hash_byte = common_opcode_state.src0_view.u8x32_view[31];
    let code_hash_version_byte = UInt8::allocated_constant(
        cs,
        zkevm_opcode_defs::definitions::versioned_hash::ContractCodeSha256Format::VERSION_BYTE,
    );
    let blob_version_byte = UInt8::allocated_constant(
        cs,
        zkevm_opcode_defs::definitions::versioned_hash::BlobSha256Format::VERSION_BYTE,
    );
    let is_code_hash_version_byte =
        UInt8::equals(cs, &versioned_hash_byte, &code_hash_version_byte);
    let is_blob_version_byte = UInt8::equals(cs, &versioned_hash_byte, &blob_version_byte);
    let version_byte_is_valid =
        Boolean::multi_or(cs, &[is_code_hash_version_byte, is_blob_version_byte]);
    let unknown_version_byte = version_byte_is_valid.negated(cs);
    let decommit_versioned_hash_exception =
        Boolean::multi_and(cs, &[unknown_version_byte, is_decommit]);
    let can_decommit = decommit_versioned_hash_exception.negated(cs);

    // but cost of decommit is determined purely by the caller
    let cost_of_decommit_call = common_opcode_state.src1_view.u32x8_view[0];

    // and check if decommit would end up a repeated one
    let boolean_false = Boolean::allocated_constant(cs, false);
    let boolean_true = Boolean::allocated_constant(cs, true);
    let zero_u32 = UInt32::allocated_constant(cs, 0);

    // now we know net cost
    let extra_cost =
        UInt32::conditionally_select(cs, is_precompile, &precompile_call_ergs_cost, &zero_u32);
    let extra_cost =
        UInt32::conditionally_select(cs, is_decommit, &cost_of_decommit_call, &extra_cost);

    let (ergs_remaining, uf) = opcode_carry_parts
        .preliminary_ergs_left
        .overflowing_sub(cs, extra_cost);
    let not_enough_ergs_for_op = uf;
    let have_enough_ergs = not_enough_ergs_for_op.negated(cs);

    // if not enough then leave only 0
    let ergs_remaining = ergs_remaining.mask_negated(cs, not_enough_ergs_for_op);
    // and we do not execute any ops in practice
    let should_apply = Boolean::multi_and(cs, &[should_apply, have_enough_ergs]);
    let should_apply_io = Boolean::multi_and(cs, &[should_apply, is_io_like_operation]);

    // we right away compute final cost of the operation here, and we will merge it into state when we do final diffs processing
    let final_pubdata_cost =
        UInt32::conditionally_select(cs, is_storage_write, &io_pubdata_cost, &zero_u32);
    let final_pubdata_cost = UInt32::conditionally_select(
        cs,
        is_precompile,
        &precompile_call_pubdata_cost,
        &final_pubdata_cost,
    );
    // NOTE: this intrinsic L1 message used L1 calldata, while our counter is for pubdata that can be propagated
    // by some other way, so we do NOT add it here

    let oracle = witness_oracle.clone();
    // we should assemble all the dependencies here, and we will use AllocateExt here
    let mut dependencies =
        Vec::with_capacity(<LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 2);
    dependencies.push(is_storage_like_access.get_variable().into());
    dependencies.push(should_apply.get_variable().into());
    dependencies.extend(Place::from_variables(log.flatten_as_variables()));

    // we always access witness, as even for writes we have to get a claimed read value!
    let read_value = UInt256::allocate_from_closure_and_dependencies(
        cs,
        move |inputs: &[F]| {
            let is_storage = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[0]);
            let execute = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[1]);
            let mut log_query =
                [F::ZERO; <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            log_query.copy_from_slice(&inputs[2..]);
            let log_query: LogQueryWitness<F> =
                CSAllocatableExt::witness_from_set_of_values(log_query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            let witness = guard.get_storage_read_witness(&log_query, is_storage, execute);
            drop(guard);

            witness
        },
        &dependencies,
    );

    let u256_zero = UInt256::zero(cs);

    let read_value =
        UInt256::conditionally_select(cs, is_storage_like_access, &read_value, &u256_zero);
    log.read_value = read_value.clone();
    // if we read then use the same value - convension!
    log.written_value =
        UInt256::conditionally_select(cs, log.rw_flag, &log.written_value, &log.read_value);

    use boojum::gadgets::traits::encodable::CircuitEncodable;
    let packed_log_forward = log.encode(cs);

    let mut packed_log_rollback = packed_log_forward;
    LogQuery::update_packing_for_rollback(cs, &mut packed_log_rollback);

    let execute_rollback = Boolean::multi_and(cs, &[should_apply, is_revertable_io]);

    let current_forward_tail = draft_vm_state
        .callstack
        .current_context
        .log_queue_forward_tail;
    let current_rollback_head = draft_vm_state
        .callstack
        .current_context
        .saved_context
        .reverted_queue_head;

    let oracle = witness_oracle.clone();
    let mut dependencies =
        Vec::with_capacity(<LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1);
    dependencies.push(execute_rollback.get_variable().into());
    dependencies.extend(Place::from_variables(log.flatten_as_variables()));

    let prev_revert_head_witness = Num::allocate_multiple_from_closure_and_dependencies(
        cs,
        move |inputs: &[F]| {
            let execute_rollback = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[0]);
            let mut log_query =
                [F::ZERO; <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            log_query.copy_from_slice(&inputs[1..]);
            let log_query: LogQueryWitness<F> =
                CSAllocatableExt::witness_from_set_of_values(log_query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            let witness = guard.get_rollback_queue_witness(&log_query, execute_rollback);
            drop(guard);

            witness
        },
        &dependencies,
    );

    let (new_forward_queue_tail, new_rollback_queue_head, sponge_relations_for_io_like_ops) =
        construct_hash_relations_for_log_and_new_queue_states(
            cs,
            &packed_log_forward,
            &packed_log_rollback,
            &current_forward_tail,
            &prev_revert_head_witness,
            &current_rollback_head,
            &should_apply_io,
            &execute_rollback,
            round_function,
        );

    // add actual update of register in case of write
    let register_value_if_storage_read = read_value;

    let mut precompile_call_result = u256_zero;
    precompile_call_result.inner[0] =
        unsafe { UInt32::from_variable_unchecked(have_enough_ergs.get_variable()) };

    // deal with decommit
    let should_decommit = Boolean::multi_and(cs, &[should_apply, is_decommit, can_decommit]);
    let mut bytecode_hash = key;
    normalize_bytecode_hash_for_decommit(cs, &mut bytecode_hash);
    let target_memory_page = opcode_carry_parts.heap_page;

    let timestamp_to_use_for_decommittment_request =
        common_opcode_state.timestamp_for_first_decommit_or_precompile_read;

    let mut decommittment_request = DecommitQuery {
        code_hash: bytecode_hash,
        page: target_memory_page,
        is_first: boolean_false,
        timestamp: timestamp_to_use_for_decommittment_request,
    };

    let oracle = witness_oracle.clone();
    // we should assemble all the dependencies here, and we will use AllocateExt here
    let mut dependencies =
        Vec::with_capacity(<DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1);
    dependencies.push(should_decommit.get_variable().into());
    dependencies.extend(Place::from_variables(
        decommittment_request.flatten_as_variables(),
    ));

    // we always access witness, as even for writes we have to get a claimed read value!
    let suggested_page = UInt32::allocate_from_closure_and_dependencies(
        cs,
        move |inputs: &[F]| {
            let should_decommit = <bool as WitnessCastable<F, F>>::cast_from_source(inputs[0]);

            let mut query =
                [F::ZERO; <DecommitQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN];
            query.copy_from_slice(&inputs[1..]);
            let query: DecommitQueryWitness<F> =
                CSAllocatableExt::witness_from_set_of_values(query);

            let mut guard = oracle.inner.write().expect("not poisoned");
            let witness = guard.get_decommittment_request_suggested_page(&query, should_decommit);
            drop(guard);

            witness
        },
        &dependencies,
    );

    let is_first = UInt32::equals(cs, &target_memory_page, &suggested_page);
    decommittment_request.is_first = is_first;
    decommittment_request.page = suggested_page;

    // form new candidate of decommit queue
    let mut sponge_relations_for_decommit = ArrayVec::<
        (
            Boolean<F>,
            [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
            [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
        ),
        MAX_SPONGES_PER_CYCLE,
    >::new();
    let (new_decommit_queue_tail, new_decommit_queue_len) = add_to_decommittment_queue_inner(
        cs,
        &mut sponge_relations_for_decommit,
        &should_decommit,
        &draft_vm_state.code_decommittment_queue_state,
        &draft_vm_state.code_decommittment_queue_length,
        &decommittment_request,
        round_function,
    );

    // we can refund a full cost if it's repeated, and only if we did decommit indeed,
    // otherwise there was out of ergs above and
    let decommit_refund = cost_of_decommit_call.mask_negated(cs, is_first);
    let decommit_refund = decommit_refund.mask(cs, should_decommit);

    let refund_value = UInt32::conditionally_select(
        cs,
        is_state_storage_access,
        &cold_warm_access_ergs_refund,
        &zero_u32,
    );
    let refund_value =
        UInt32::conditionally_select(cs, is_decommit, &decommit_refund, &refund_value);

    // apply refund
    let ergs_remaining = ergs_remaining.add_no_overflow(cs, refund_value);

    // assemble dst0 candidates
    // one for io-like and precompile call
    let register_value = UInt256::conditionally_select(
        cs,
        is_io_read_like,
        &register_value_if_storage_read,
        &precompile_call_result,
    );
    let dst0_for_io_ops_and_precompile_call = VMRegister {
        value: register_value,
        is_pointer: boolean_false,
    };
    // another one for decommit. It's a fat pointer!
    let mut register_value = zero_u256;
    // we have 0 offset and 0 start, and only need length and memory page
    // page
    register_value.inner[1] = suggested_page;
    // length is set to the full "free" heap space, and caller is responsible to truncate it
    let preimage_len_in_bytes = UInt32::allocated_constant(
        cs,
        zkevm_opcode_defs::system_params::NEW_KERNEL_FRAME_MEMORY_STIPEND,
    );
    register_value.inner[3] = preimage_len_in_bytes;

    let mut dst_0_for_decommit = VMRegister {
        value: register_value,
        is_pointer: boolean_true,
    };
    // or it's empty if decommit didn't work
    let decommit_failed = Boolean::multi_or(
        cs,
        &[decommit_versioned_hash_exception, not_enough_ergs_for_op],
    );
    dst_0_for_decommit.conditionally_erase(cs, decommit_failed);

    let selected_dst_0_value = VMRegister::conditionally_select(
        cs,
        is_decommit,
        &dst_0_for_decommit,
        &dst0_for_io_ops_and_precompile_call,
    );

    let old_forward_queue_length = draft_vm_state
        .callstack
        .current_context
        .log_queue_forward_part_length;

    let new_forward_queue_length_candidate =
        unsafe { old_forward_queue_length.increment_unchecked(cs) };
    let new_forward_queue_length = UInt32::conditionally_select(
        cs,
        should_apply,
        &new_forward_queue_length_candidate,
        &old_forward_queue_length,
    );

    let old_revert_queue_length = draft_vm_state
        .callstack
        .current_context
        .saved_context
        .reverted_queue_segment_len;

    let new_revert_queue_length_candidate =
        unsafe { old_revert_queue_length.increment_unchecked(cs) };
    let new_revert_queue_length = UInt32::conditionally_select(
        cs,
        execute_rollback,
        &new_revert_queue_length_candidate,
        &old_revert_queue_length,
    );

    let can_update_dst0 = Boolean::multi_or(cs, &[is_nonrevertable_io, is_decommit]);
    let should_update_dst0 = Boolean::multi_and(cs, &[can_update_dst0, should_apply]);

    if crate::config::CIRCUIT_VERSOBE {
        if should_apply.witness_hook(&*cs)().unwrap() {
            dbg!(should_update_dst0.witness_hook(&*cs)().unwrap());
            dbg!(selected_dst_0_value.witness_hook(&*cs)().unwrap());
        }
    }

    let can_write_into_memory =
        STORAGE_READ_OPCODE.can_write_dst0_into_memory(SUPPORTED_ISA_VERSION);
    diffs_accumulator.dst_0_values.push((
        can_write_into_memory,
        should_update_dst0,
        selected_dst_0_value,
    ));

    diffs_accumulator.log_queue_forward_candidates.push((
        should_apply,
        new_forward_queue_length,
        new_forward_queue_tail,
    ));

    diffs_accumulator.log_queue_rollback_candidates.push((
        should_apply,
        new_revert_queue_length,
        new_rollback_queue_head,
    ));

    diffs_accumulator
        .new_ergs_left_candidates
        .push((should_apply, ergs_remaining));

    assert!(STORAGE_READ_OPCODE.can_have_src0_from_mem(SUPPORTED_ISA_VERSION) == false);
    assert!(STORAGE_READ_OPCODE.can_write_dst0_into_memory(SUPPORTED_ISA_VERSION) == false);

    diffs_accumulator.sponge_candidates_to_run.push((
        false,
        false,
        should_apply_io,
        sponge_relations_for_io_like_ops,
    ));
    diffs_accumulator.sponge_candidates_to_run.push((
        false,
        false,
        should_decommit,
        sponge_relations_for_decommit,
    ));

    let exception = Boolean::multi_and(cs, &[decommit_versioned_hash_exception, should_apply]);
    diffs_accumulator.pending_exceptions.push(exception);

    diffs_accumulator.decommitment_queue_candidates.push((
        should_apply,
        new_decommit_queue_len,
        new_decommit_queue_tail,
    ));

    assert!(diffs_accumulator.pubdata_cost.is_none());
    diffs_accumulator.pubdata_cost = Some((should_apply, final_pubdata_cost));
}

use crate::base_structures::vm_state::FULL_SPONGE_QUEUE_STATE_WIDTH;
use crate::main_vm::state_diffs::MAX_SPONGES_PER_CYCLE;
use arrayvec::ArrayVec;

fn construct_hash_relations_for_log_and_new_queue_states<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    forward_packed_log: &[Variable; LOG_QUERY_PACKED_WIDTH],
    forward_rollback_log: &[Variable; LOG_QUERY_PACKED_WIDTH],
    forward_queue_tail: &[Num<F>; 4],
    claimed_rollback_head: &[Num<F>; 4],
    current_rollback_head: &[Num<F>; 4],
    should_execute_either: &Boolean<F>,
    should_execute_rollback: &Boolean<F>,
    _round_function: &R,
) -> (
    [Num<F>; 4],
    [Num<F>; 4],
    ArrayVec<
        (
            Boolean<F>,
            [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
            [Num<F>; FULL_SPONGE_QUEUE_STATE_WIDTH],
        ),
        MAX_SPONGES_PER_CYCLE,
    >,
) {
    // we should be clever and simultaneously produce 2 relations:
    // - 2 common sponges for forward/rollback that only touch the encodings
    // - 1 unique sponge for forward
    // - 1 unique sponge for rollback

    // check that we only differ at the very end
    for (a, b) in forward_packed_log[..ROLLBACK_PACKING_FLAG_VARIABLE_IDX]
        .iter()
        .zip(forward_rollback_log[..ROLLBACK_PACKING_FLAG_VARIABLE_IDX].iter())
    {
        debug_assert_eq!(a, b);
    }

    // we absort with replacement

    let mut current_state = R::create_empty_state(cs);
    // TODO: may be decide on length specialization

    // absorb by replacement
    let round_0_initial = [
        forward_packed_log[0],
        forward_packed_log[1],
        forward_packed_log[2],
        forward_packed_log[3],
        forward_packed_log[4],
        forward_packed_log[5],
        forward_packed_log[6],
        forward_packed_log[7],
        current_state[8],
        current_state[9],
        current_state[10],
        current_state[11],
    ];

    use boojum::gadgets::round_function::simulate_round_function;

    let round_0_final =
        simulate_round_function::<_, _, 8, 12, 4, R>(cs, round_0_initial, *should_execute_either);

    current_state = round_0_final;

    // absorb by replacement
    let round_1_initial = [
        forward_packed_log[8],
        forward_packed_log[9],
        forward_packed_log[10],
        forward_packed_log[11],
        forward_packed_log[12],
        forward_packed_log[13],
        forward_packed_log[14],
        forward_packed_log[15],
        current_state[8],
        current_state[9],
        current_state[10],
        current_state[11],
    ];

    let round_1_final =
        simulate_round_function::<_, _, 8, 12, 4, R>(cs, round_1_initial, *should_execute_either);

    current_state = round_1_final;

    // absorb by replacement
    let round_2_initial_forward = [
        forward_packed_log[16],
        forward_packed_log[17],
        forward_packed_log[18],
        forward_packed_log[19],
        forward_queue_tail[0].get_variable(),
        forward_queue_tail[1].get_variable(),
        forward_queue_tail[2].get_variable(),
        forward_queue_tail[3].get_variable(),
        current_state[8],
        current_state[9],
        current_state[10],
        current_state[11],
    ];

    let forward_round_2_final = simulate_round_function::<_, _, 8, 12, 4, R>(
        cs,
        round_2_initial_forward,
        *should_execute_either,
    );

    // absorb by replacement
    let round_2_initial_rollback = [
        forward_rollback_log[16],
        forward_rollback_log[17],
        forward_rollback_log[18],
        forward_rollback_log[19],
        claimed_rollback_head[0].get_variable(),
        claimed_rollback_head[1].get_variable(),
        claimed_rollback_head[2].get_variable(),
        claimed_rollback_head[3].get_variable(),
        current_state[8],
        current_state[9],
        current_state[10],
        current_state[11],
    ];

    let rollback_round_2_final = simulate_round_function::<_, _, 8, 12, 4, R>(
        cs,
        round_2_initial_rollback,
        *should_execute_either,
    ); // at the moment we do not mark which sponges are actually used and which are not
       // in the opcode, so we properly simulate all of them

    let new_forward_tail_candidate = [
        forward_round_2_final[0],
        forward_round_2_final[1],
        forward_round_2_final[2],
        forward_round_2_final[3],
    ];

    let new_forward_tail_candidate = new_forward_tail_candidate.map(|el| Num::from_variable(el));

    let simulated_rollback_head = [
        rollback_round_2_final[0],
        rollback_round_2_final[1],
        rollback_round_2_final[2],
        rollback_round_2_final[3],
    ];

    let simulated_rollback_head = simulated_rollback_head.map(|el| Num::from_variable(el));

    // select forward

    let new_forward_queue_tail = Num::parallel_select(
        cs,
        *should_execute_either,
        &new_forward_tail_candidate,
        &forward_queue_tail,
    );

    // select rollback

    let new_rollback_queue_head = Num::parallel_select(
        cs,
        *should_execute_rollback,
        &claimed_rollback_head,
        &current_rollback_head,
    );

    for (a, b) in simulated_rollback_head
        .iter()
        .zip(current_rollback_head.iter())
    {
        Num::conditionally_enforce_equal(cs, *should_execute_rollback, a, b);
    }

    let mut relations = ArrayVec::new();
    relations.push((
        *should_execute_either,
        round_0_initial.map(|el| Num::from_variable(el)),
        round_0_final.map(|el| Num::from_variable(el)),
    ));

    relations.push((
        *should_execute_either,
        round_1_initial.map(|el| Num::from_variable(el)),
        round_1_final.map(|el| Num::from_variable(el)),
    ));

    relations.push((
        *should_execute_either,
        round_2_initial_forward.map(|el| Num::from_variable(el)),
        forward_round_2_final.map(|el| Num::from_variable(el)),
    ));

    relations.push((
        *should_execute_rollback,
        round_2_initial_rollback.map(|el| Num::from_variable(el)),
        rollback_round_2_final.map(|el| Num::from_variable(el)),
    ));

    (new_forward_queue_tail, new_rollback_queue_head, relations)
}
