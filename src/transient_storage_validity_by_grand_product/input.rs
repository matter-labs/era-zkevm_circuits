use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use crate::DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS;
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::{
    gadgets::{
        boolean::Boolean,
        num::*,
        queue::*,
        traits::{
            allocatable::*, encodable::CircuitVarLengthEncodable, selectable::Selectable,
            witnessable::WitnessHookable,
        },
        u256::*,
        u32::*,
    },
    serde_utils::BigArraySerde,
};
use cs_derive::*;
use derivative::*;

use super::TimestampedStorageLogRecord;

pub const TRANSIENT_STORAGE_VALIDITY_CHECK_PACKED_KEY_LENGTH: usize = 1 + 1 + 5 + 8;

// FSM

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct TransientStorageDeduplicatorFSMInputOutput<F: SmallField> {
    pub lhs_accumulator: [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
    pub rhs_accumulator: [Num<F>; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
    pub current_unsorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub current_intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub cycle_idx: UInt32<F>,
    pub previous_packed_key: [UInt32<F>; TRANSIENT_STORAGE_VALIDITY_CHECK_PACKED_KEY_LENGTH], // it captures tx number, shard id, address and key
    pub previous_timestamp: UInt32<F>,
    pub this_cell_current_value: UInt256<F>,
    pub this_cell_current_depth: UInt32<F>,
}

impl<F: SmallField> CSPlaceholder<F> for TransientStorageDeduplicatorFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_num = Num::<F>::zero(cs);
        let zero_u32 = UInt32::zero(cs);
        let zero_u256 = UInt256::zero(cs);

        Self {
            lhs_accumulator: [zero_num; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
            rhs_accumulator: [zero_num; DEFAULT_NUM_PERMUTATION_ARGUMENT_REPETITIONS],
            current_unsorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            current_intermediate_sorted_queue_state:
                QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            cycle_idx: zero_u32,
            previous_packed_key: [zero_u32; TRANSIENT_STORAGE_VALIDITY_CHECK_PACKED_KEY_LENGTH],
            previous_timestamp: zero_u32,
            this_cell_current_value: zero_u256,
            this_cell_current_depth: zero_u32,
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Debug)]
pub struct TransientStorageDeduplicatorInputData<F: SmallField> {
    pub unsorted_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub intermediate_sorted_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for TransientStorageDeduplicatorInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            unsorted_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            intermediate_sorted_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type TransientStorageDeduplicatorInputOutput<F> = crate::fsm_input_output::ClosedFormInput<
    F,
    TransientStorageDeduplicatorFSMInputOutput<F>,
    TransientStorageDeduplicatorInputData<F>,
    (),
>;
pub type TransientStorageDeduplicatorInputOutputWitness<F> =
    crate::fsm_input_output::ClosedFormInputWitness<
        F,
        TransientStorageDeduplicatorFSMInputOutput<F>,
        TransientStorageDeduplicatorInputData<F>,
        (),
    >;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct TransientStorageDeduplicatorInstanceWitness<F: SmallField> {
    pub closed_form_input: TransientStorageDeduplicatorInputOutputWitness<F>,
    pub unsorted_queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
    pub intermediate_sorted_queue_witness:
        CircuitQueueRawWitness<F, TimestampedStorageLogRecord<F>, 4, LOG_QUERY_PACKED_WIDTH>,
}
