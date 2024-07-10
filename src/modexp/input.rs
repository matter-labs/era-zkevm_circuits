use boojum::cs::traits::cs::ConstraintSystem;
use std::collections::VecDeque;

use super::*;
use crate::base_structures::log_query::LogQuery;
use crate::base_structures::precompile_input_outputs::*;
use crate::base_structures::vm_state::*;
use crate::fsm_input_output::{ClosedFormInput, ClosedFormInputWitness};
use boojum::cs::Variable;
use boojum::field::SmallField;
use boojum::gadgets::queue::*;
use boojum::gadgets::traits::allocatable::CSAllocatable;
use boojum::gadgets::traits::allocatable::CSPlaceholder;
use boojum::gadgets::traits::auxiliary::PrettyComparison;
use boojum::gadgets::traits::encodable::CircuitVarLengthEncodable;
use cs_derive::{CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable};
use derivative::Derivative;
use serde::{Deserialize, Serialize};

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct ModexpCircuitFSMInputOutput<F: SmallField> {
    pub log_queue_state: QueueState<F, QUEUE_STATE_WIDTH>,
    pub memory_queue_state: QueueState<F, FULL_SPONGE_QUEUE_STATE_WIDTH>,
}

impl<F> CSPlaceholder<F> for ModexpCircuitFSMInputOutput<F>
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

pub type ModexpCircuitInputOutput<F> = ClosedFormInput<
    F,
    ModexpCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;
pub type ModexpCircuitInputOutputWitness<F> = ClosedFormInputWitness<
    F,
    ModexpCircuitFSMInputOutput<F>,
    PrecompileFunctionInputData<F>,
    PrecompileFunctionOutputData<F>,
>;

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct ModexpCircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: ModexpCircuitInputOutputWitness<F>,
    pub requests_queue_witness: CircuitQueueRawWitness<F, LogQuery<F>, 4, LOG_QUERY_PACKED_WIDTH>,
    pub memory_reads_witness: VecDeque<[U256; MEMORY_QUERIES_PER_CALL]>,
}
