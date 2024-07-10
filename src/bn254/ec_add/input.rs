use std::collections::VecDeque;

use super::*;
use crate::base_structures::precompile_input_outputs::*;
use crate::base_structures::vm_state::*;
use boojum::cs::Variable;
use boojum::field::SmallField;
use boojum::gadgets::queue::*;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::allocatable::CSPlaceholder;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::gadgets::traits::encodable::CircuitVarLengthEncodable;
use derivative::Derivative;
use serde::{Deserialize, Serialize};

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EcAddCircuitFSMInputOutput<F: SmallField> {
    pub log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub memory_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F> CSPlaceholder<F> for EcAddCircuitFSMInputOutput<F>
where
    F: SmallField,
{
    fn placeholder<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self {
            log_queue_state: QueueState::<F, QUEUE_STATE_WIDTH>::placeholder(cs),
            memory_queue_state: QueueState::<F, FULL_SPONGE_QUEUE_STATE_WIDTH>::placeholder(cs),
        }
    }
}

pub type EcAddCircuitInputOutput<F> = ClosedFormInput<
    F,
    EcAddCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;
pub type EcAddCircuitInputOutputWitness<F> = ClosedFormInputWitness<
    F,
    EcAddCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct EcAddCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: EcAddCircuitInputOutputWitness<F>,
    pub requests_queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
    pub memory_reads_witness: VecDeque<[U256; MEMORY_QUERIES_PER_CALL]>,
}
