use std::collections::HashMap;

use crate::base_structures::{
    log_query::{LogQuery, LOG_QUERY_PACKED_WIDTH},
    vm_state::*,
};
use crate::demux_log_queue::DemuxOutput;
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
use boojum::serde_utils::BigArraySerde;
use cs_derive::*;
use derivative::*;

use super::NUM_DEMUX_OUTPUTS;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct LogDemuxerFSMInputOutput<F: SmallField> {
    pub initial_log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub output_queue_states: [QueueState<F, QUEUE_STATE_WIDTH>; NUM_DEMUX_OUTPUTS],
}

impl<F: SmallField> CSPlaceholder<F> for LogDemuxerFSMInputOutput<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let placeholder_state = QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs);
        Self {
            initial_log_queue_state: placeholder_state,
            output_queue_states: [placeholder_state; NUM_DEMUX_OUTPUTS],
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
    pub output_queue_states: [QueueState<F, QUEUE_STATE_WIDTH>; NUM_DEMUX_OUTPUTS],
}

impl<F: SmallField> CSPlaceholder<F> for LogDemuxerOutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let placeholder_state = QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs);
        Self {
            output_queue_states: [placeholder_state; NUM_DEMUX_OUTPUTS],
        }
    }
}

impl<F: SmallField> LogDemuxerOutputData<F> {
    pub fn all_output_queues_refs(
        &self,
    ) -> HashMap<DemuxOutput, &QueueState<F, QUEUE_STATE_WIDTH>> {
        let tuples = [
            (
                DemuxOutput::RollupStorage,
                &self.output_queue_states[DemuxOutput::RollupStorage as usize],
            ),
            (
                DemuxOutput::PorterStorage,
                &self.output_queue_states[DemuxOutput::PorterStorage as usize],
            ),
            (
                DemuxOutput::Events,
                &self.output_queue_states[DemuxOutput::Events as usize],
            ),
            (
                DemuxOutput::L2ToL1Messages,
                &self.output_queue_states[DemuxOutput::L2ToL1Messages as usize],
            ),
            (
                DemuxOutput::Keccak,
                &self.output_queue_states[DemuxOutput::Keccak as usize],
            ),
            (
                DemuxOutput::Sha256,
                &self.output_queue_states[DemuxOutput::Sha256 as usize],
            ),
            (
                DemuxOutput::ECRecover,
                &self.output_queue_states[DemuxOutput::ECRecover as usize],
            ),
            (
                DemuxOutput::Secp256r1Verify,
                &self.output_queue_states[DemuxOutput::Secp256r1Verify as usize],
            ),
        ];
        assert_eq!(tuples.len(), NUM_DEMUX_OUTPUTS);

        HashMap::from_iter(tuples.into_iter())
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
