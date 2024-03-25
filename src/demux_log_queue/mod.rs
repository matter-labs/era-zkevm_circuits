use std::collections::{HashMap, HashSet};

use super::*;

pub mod input;

use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use crate::fsm_input_output::ClosedFormInputCompactForm;
use arrayvec::ArrayVec;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::{gates::*, traits::cs::ConstraintSystem};
use boojum::field::SmallField;

use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::gadgets::{
    boolean::Boolean,
    num::Num,
    queue::*,
    traits::{
        allocatable::CSAllocatableExt, encodable::CircuitEncodableExt, selectable::Selectable,
    },
    u160::*,
};

use zkevm_opcode_defs::system_params::*;

use crate::{
    demux_log_queue::input::*,
    fsm_input_output::{circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH, *},
};

pub type StorageLogQueue<F, R> = CircuitQueue<F, LogQuery<F>, 8, 12, 4, 4, 20, R>;
pub type StorageLogQueueWitness<F> =
    CircuitQueueWitness<F, LogQuery<F>, QUEUE_STATE_WIDTH, LOG_QUERY_PACKED_WIDTH>;

#[repr(usize)]
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum DemuxOutput {
    RollupStorage = 0,
    PorterStorage,
    Events,
    L2ToL1Messages,
    Keccak,
    Sha256,
    ECRecover,
    Secp256r1Verify,
    TransientStorage,
}

pub const NUM_DEMUX_OUTPUTS: usize = DemuxOutput::TransientStorage as usize + 1;

pub const ALL_DEMUX_OUTPUTS: [DemuxOutput; NUM_DEMUX_OUTPUTS] = [
    DemuxOutput::RollupStorage,
    DemuxOutput::PorterStorage,
    DemuxOutput::Events,
    DemuxOutput::L2ToL1Messages,
    DemuxOutput::Keccak,
    DemuxOutput::Sha256,
    DemuxOutput::ECRecover,
    DemuxOutput::Secp256r1Verify,
    DemuxOutput::TransientStorage,
];

impl DemuxOutput {
    pub fn is_implemented(&self) -> bool {
        match self {
            Self::PorterStorage => false,
            _ => true,
        }
    }

    pub fn aux_byte(&self) -> u8 {
        match self {
            Self::RollupStorage | Self::PorterStorage => STORAGE_AUX_BYTE,
            Self::Events => EVENT_AUX_BYTE,
            Self::L2ToL1Messages => L1_MESSAGE_AUX_BYTE,
            Self::TransientStorage => TRANSIENT_STORAGE_AUX_BYTE,
            _ => PRECOMPILE_AUX_BYTE,
        }
    }

    pub fn precompile_address(&self) -> Option<zkevm_opcode_defs::ethereum_types::H160> {
        match self {
            Self::Keccak => Some(*zkevm_opcode_defs::system_params::KECCAK256_ROUND_FUNCTION_PRECOMPILE_FORMAL_ADDRESS),
            Self::Sha256 => Some(*zkevm_opcode_defs::system_params::SHA256_ROUND_FUNCTION_PRECOMPILE_FORMAL_ADDRESS),
            Self::ECRecover => Some(*zkevm_opcode_defs::system_params::ECRECOVER_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS),
            Self::Secp256r1Verify => Some(*zkevm_opcode_defs::system_params::SECP256R1_VERIFY_INNER_FUNCTION_PRECOMPILE_FORMAL_ADDRESS),
            _ => None,
        }
    }

    pub fn shard_id(&self) -> Option<u8> {
        match self {
            Self::RollupStorage => Some(0u8),
            Self::PorterStorage => Some(1u8),
            _ => None,
        }
    }
}

pub fn demultiplex_storage_logs_enty_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: LogDemuxerCircuitInstanceWitness<F>,
    round_function: &R,
    limit: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let LogDemuxerCircuitInstanceWitness {
        closed_form_input,
        initial_queue_witness,
    } = witness;

    let mut structured_input =
        LogDemuxerInputOutput::alloc_ignoring_outputs(cs, closed_form_input.clone());

    // passthrough must be trivial
    structured_input
        .observable_input
        .initial_log_queue_state
        .enforce_trivial_head(cs);

    let state = QueueState::conditionally_select(
        cs,
        structured_input.start_flag,
        &structured_input.observable_input.initial_log_queue_state,
        &structured_input.hidden_fsm_input.initial_log_queue_state,
    );
    let mut initial_queue = StorageLogQueue::<F, R>::from_state(cs, state);
    use std::sync::Arc;
    let initial_queue_witness = CircuitQueueWitness::from_inner_witness(initial_queue_witness);
    initial_queue.witness = Arc::new(initial_queue_witness);

    // for the rest it's just select between empty or from FSM
    let queue_states_from_fsm = &structured_input.hidden_fsm_input.output_queue_states;

    let empty_state = QueueState::empty(cs);
    let mut queue_states = queue_states_from_fsm.map(|el| {
        let state =
            QueueState::conditionally_select(cs, structured_input.start_flag, &empty_state, &el);
        StorageLogQueue::<F, R>::from_state(cs, state)
    });

    demultiplex_storage_logs_inner(cs, &mut initial_queue, &mut queue_states, limit);

    use boojum::gadgets::traits::allocatable::CSPlaceholder;
    // form the final state
    structured_input.observable_output = LogDemuxerOutputData::placeholder(cs);

    let completed = initial_queue.is_empty(cs);
    structured_input.completion_flag = completed;

    structured_input.hidden_fsm_output.initial_log_queue_state = initial_queue.into_state();

    structured_input.hidden_fsm_output.output_queue_states = queue_states.map(|el| el.into_state());

    let porter_storage_queue =
        structured_input.hidden_fsm_output.output_queue_states[DemuxOutput::PorterStorage as usize];
    let porter_storage_queue_is_empty = porter_storage_queue.tail.length.is_zero(cs);
    let boolean_true = Boolean::allocated_constant(cs, true);
    Boolean::enforce_equal(cs, &porter_storage_queue_is_empty, &boolean_true);

    // copy into observable output
    for (dst, src) in structured_input
        .observable_output
        .output_queue_states
        .iter_mut()
        .zip(
            structured_input
                .hidden_fsm_output
                .output_queue_states
                .iter(),
        )
    {
        *dst = QueueState::conditionally_select(cs, completed, src, &*dst);
    }

    // self-check
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

pub fn demultiplex_storage_logs_inner<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    storage_log_queue: &mut StorageLogQueue<F, R>,
    output_queues: &mut [StorageLogQueue<F, R>; NUM_DEMUX_OUTPUTS],
    limit: usize,
) where
    [(); <LogQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    assert!(limit <= u32::MAX as usize);

    let boolean_false = Boolean::allocated_constant(cs, false);

    let mut all_different_aux_bytes = vec![];
    let mut add_different_addresses = vec![];
    let mut all_different_shard_ids = vec![];

    let mut aux_byte_set = HashSet::new();
    let mut aux_different_addresses_set = HashSet::new();
    let mut aux_shard_ids_set = HashSet::new();

    for el in ALL_DEMUX_OUTPUTS.into_iter() {
        let aux_byte = el.aux_byte();
        if aux_byte_set.contains(&aux_byte) == false {
            aux_byte_set.insert(aux_byte);
            all_different_aux_bytes.push((aux_byte, UInt8::allocated_constant(cs, aux_byte)));
        }
        if let Some(address) = el.precompile_address() {
            if aux_different_addresses_set.contains(&address) == false {
                aux_different_addresses_set.insert(address);
                add_different_addresses.push((address, UInt160::allocated_constant(cs, address)));
            }
        }
        if let Some(shard_id) = el.shard_id() {
            if aux_shard_ids_set.contains(&shard_id) == false {
                aux_shard_ids_set.insert(shard_id);
                all_different_shard_ids.push((shard_id, UInt8::allocated_constant(cs, shard_id)));
            }
        }
    }

    let mut aux_byte_equality_map = HashMap::new();
    let mut address_equality_map = HashMap::new();
    let mut shard_id_equality_map = HashMap::new();

    for _ in 0..limit {
        assert!(aux_byte_equality_map.is_empty());
        assert!(address_equality_map.is_empty());
        assert!(shard_id_equality_map.is_empty());

        let queue_is_empty = storage_log_queue.is_empty(cs);
        let execute = queue_is_empty.negated(cs);
        let (popped, _) = storage_log_queue.pop_front(cs, execute);

        // precompute all comparisons

        for (constant, allocated) in all_different_aux_bytes.iter() {
            let equal = UInt8::equals(cs, allocated, &popped.aux_byte);
            let existing = aux_byte_equality_map.insert(*constant, equal);
            assert!(existing.is_none());
        }

        for (constant, allocated) in add_different_addresses.iter() {
            let equal = UInt160::equals(cs, allocated, &popped.address);
            let existing = address_equality_map.insert(*constant, equal);
            assert!(existing.is_none());
        }

        for (constant, allocated) in all_different_shard_ids.iter() {
            let equal = UInt8::equals(cs, allocated, &popped.shard_id);
            let existing = shard_id_equality_map.insert(*constant, equal);
            assert!(existing.is_none());
        }

        let mut bitmasks = [boolean_false; NUM_DEMUX_OUTPUTS];

        const MAX_FLAGS: usize = 4;

        for el in ALL_DEMUX_OUTPUTS.into_iter() {
            let mut flags = ArrayVec::<Boolean<F>, MAX_FLAGS>::new();
            flags.push(execute);

            let aux_byte = el.aux_byte();
            flags.push(aux_byte_equality_map[&aux_byte]);

            if let Some(address) = el.precompile_address() {
                flags.push(address_equality_map[&address]);
            }

            if let Some(shard_id) = el.shard_id() {
                flags.push(shard_id_equality_map[&shard_id]);
            }

            bitmasks[el as usize] = Boolean::multi_and(cs, &flags[..]);
        }

        push_with_optimize(cs, output_queues, bitmasks, popped);

        // if crate::config::CIRCUIT_VERSOBE {
        //     dbg!(bitmasks.witness_hook(cs)().unwrap());
        // }

        let is_bitmask = check_if_bitmask_or_if_empty(cs, bitmasks);
        is_bitmask.conditionally_enforce_true(cs, execute);

        aux_byte_equality_map.clear();
        address_equality_map.clear();
        shard_id_equality_map.clear();
    }

    storage_log_queue.enforce_consistency(cs);

    // checks in "Drop" interact badly with some tools, so we check it during testing instead
    // debug_assert!(optimizer.is_fresh());
}

pub fn push_with_optimize<
    F: SmallField,
    CS: ConstraintSystem<F>,
    EL: CircuitEncodableExt<F, N>,
    const N: usize,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    const NUM_QUEUES: usize,
>(
    cs: &mut CS,
    output_queues: &mut [StorageLogQueue<F, R>; NUM_QUEUES],
    bitmask: [Boolean<F>; NUM_QUEUES],
    value_for_encoding: EL,
) where
    [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let mut states = output_queues.iter().map(|x| x.into_state());
    let mut state = states.next().unwrap();

    for (bit, next_state) in bitmask.iter().skip(1).zip(states) {
        state = QueueState::conditionally_select(cs, *bit, &next_state, &state);
    }

    let mut exec_queue = CircuitQueue::<F, EL, 8, 12, 4, 4, N, R>::from_raw_parts(
        cs,
        state.head,
        state.tail.tail,
        state.tail.length,
    );

    let boolean_true = Boolean::allocated_constant(cs, true);
    exec_queue.push(cs, value_for_encoding, boolean_true);

    for (bit, queue) in bitmask.into_iter().zip(output_queues.iter_mut()) {
        // We don't need to update head
        queue.tail = <[Num<F>; 4]>::conditionally_select(cs, bit, &exec_queue.tail, &queue.tail);
        queue.length = UInt32::conditionally_select(cs, bit, &exec_queue.length, &queue.length);
    }
}

pub fn check_if_bitmask_or_if_empty<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    mask: [Boolean<F>; N],
) -> Boolean<F> {
    let lc: [_; N] = mask.map(|el| (el.get_variable(), F::ONE));

    let lc = Num::linear_combination(cs, &lc);

    let one = Num::from_variable(cs.allocate_constant(F::ONE));
    let is_one = Num::equals(cs, &lc, &one);
    let is_zero = lc.is_zero(cs);
    let is_boolean = Boolean::multi_or(cs, &[is_zero, is_one]);

    is_boolean
}

#[cfg(test)]
mod tests {
    use super::*;
    use boojum::algebraic_props::poseidon2_parameters::Poseidon2GoldilocksExternalMatrix;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::CSGeometry;
    use boojum::cs::*;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::tables::*;
    use boojum::gadgets::u160::UInt160;
    use boojum::gadgets::u256::UInt256;
    use boojum::gadgets::u32::UInt32;
    use boojum::gadgets::u8::UInt8;
    use boojum::implementations::poseidon2::Poseidon2Goldilocks;
    use boojum::worker::Worker;
    use ethereum_types::{Address, U256};
    type F = GoldilocksField;
    type P = GoldilocksField;

    #[test]
    fn test_demultiplex_storage_logs_inner() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 100,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
        };

        use boojum::cs::cs_builder::*;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: 8,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = BooleanConstraintGate::configure_builder(
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
            let builder = SelectionGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );
            let builder = DotProductGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksExternalMatrix>::configure_builder(builder,GatePlacementStrategy::UseGeneralPurposeColumns);
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        use boojum::config::DevCSConfig;
        use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, 1 << 20);
        use boojum::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(1 << 26);

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let cs = &mut owned_cs;

        // start test
        let execute = Boolean::allocated_constant(cs, true);

        let mut storage_log_queue = StorageLogQueue::<F, Poseidon2Goldilocks>::empty(cs);
        let unsorted_input = witness_input_unsorted(cs);
        for el in unsorted_input {
            storage_log_queue.push(cs, el, execute);
        }

        let mut output = std::array::from_fn(|_| StorageLogQueue::empty(cs));
        let limit = 16;
        demultiplex_storage_logs_inner(cs, &mut storage_log_queue, &mut output, limit);

        cs.pad_and_shrink();
        let worker = Worker::new();
        let mut owned_cs = owned_cs.into_assembly::<std::alloc::Global>();
        owned_cs.print_gate_stats();
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    fn witness_input_unsorted<CS: ConstraintSystem<F>>(cs: &mut CS) -> Vec<LogQuery<F>> {
        let mut unsorted_querie = vec![];
        let bool_false = Boolean::allocated_constant(cs, false);
        let bool_true = Boolean::allocated_constant(cs, true);
        let zero_8 = UInt8::allocated_constant(cs, 0);
        let zero_32 = UInt32::allocated_constant(cs, 0);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 1205),
        };

        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("1").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 1425),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 1609),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("7").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 1777),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 1969),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("5").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2253),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32769)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("10").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_true,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2357),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2429),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("4").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2681),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32769)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("9").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2797),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32769)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("9").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_true,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2829),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 2901),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("3").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 3089),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32769)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("8").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_true,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 3193),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32770)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("32779").unwrap()),
            read_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            written_value: UInt256::allocated_constant(
                cs,
                U256::from_dec_str(
                    "452319300877325313852488925888724764263521004047156906617735320131041551860",
                )
                .unwrap(),
            ),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 3265),
        };
        unsorted_querie.push(q);

        let q = LogQuery::<F> {
            address: UInt160::allocated_constant(cs, Address::from_low_u64_le(32779)),
            key: UInt256::allocated_constant(cs, U256::from_dec_str("2").unwrap()),
            read_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            written_value: UInt256::allocated_constant(cs, U256::from_dec_str("0").unwrap()),
            rw_flag: bool_false,
            aux_byte: zero_8,
            rollback: bool_false,
            is_service: bool_false,
            shard_id: zero_8,
            tx_number_in_block: zero_32,
            timestamp: UInt32::allocated_constant(cs, 3421),
        };
        unsorted_querie.push(q);

        unsorted_querie
    }
}
