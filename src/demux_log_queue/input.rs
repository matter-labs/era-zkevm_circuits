use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::gadgets::{
    boolean::Boolean,
    queue::*,
    traits::{
        allocatable::*, encodable::CircuitVarLengthEncodable, selectable::Selectable,
        witnessable::WitnessHookable,
    },
};
use cs_derive::*;
use derivative::*;

pub const NUM_OUTPUT_QUEUES: usize = 6;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct LogDemuxerFSMInputOutput<F: SmallField> {
    pub initial_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub storage_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub events_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub l1messages_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub keccak256_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub sha256_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub ecrecover_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for LogDemuxerFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            initial_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            storage_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            events_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            l1messages_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            keccak256_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            sha256_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            ecrecover_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct LogDemuxerInputData<F: SmallField> {
    pub initial_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for LogDemuxerInputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            initial_log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct LogDemuxerOutputData<F: SmallField> {
    pub storage_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub events_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub l1messages_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub keccak256_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub sha256_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub ecrecover_access_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
}

impl<F: SmallField> CSPlaceholder<F> for LogDemuxerOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            storage_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            events_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            l1messages_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            keccak256_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            sha256_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            ecrecover_access_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

impl<F: SmallField> LogDemuxerOutputData<F> {
    pub fn all_output_queues_refs(&self) -> [&QueueState<F, QUEUE_STATE_WIDTH>; NUM_OUTPUT_QUEUES] {
        [
            &self.storage_access_queue_state,
            &self.keccak256_access_queue_state,
            &self.sha256_access_queue_state,
            &self.ecrecover_access_queue_state,
            &self.events_access_queue_state,
            &self.l1messages_access_queue_state,
        ]
    }
}

pub type LogDemuxerInputOutput<F> = crate::fsm_input_output::ClosedFormInput<
    F,
    LogDemuxerFSMInputOutput<F>,
    LogDemuxerInputData<F>,
    LogDemuxerOutputData<F>,
>;

pub type LogDemuxerInputOutputWitness<F> = crate::fsm_input_output::ClosedFormInputWitness<
    F,
    LogDemuxerFSMInputOutput<F>,
    LogDemuxerInputData<F>,
    LogDemuxerOutputData<F>,
>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct LogDemuxerCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: LogDemuxerInputOutputWitness<F>,
    pub initial_queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
}
