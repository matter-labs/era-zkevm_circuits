use std::collections::VecDeque;

use super::*;

use boojum::cs::{traits::cs::ConstraintSystem, Variable};
use boojum::field::SmallField;
use boojum::gadgets::keccak256;
use boojum::gadgets::traits::auxiliary::PrettyComparison;

use boojum::gadgets::u8::UInt8;
use boojum::gadgets::{
    boolean::Boolean,
    traits::{
        encodable::CircuitVarLengthEncodable, selectable::Selectable, witnessable::WitnessHookable,
    },
};
use boojum::serde_utils::BigArraySerde;
use cs_derive::*;

pub const BLOB_CHUNK_SIZE: usize = 31;
pub const ELEMENTS_PER_4844_BLOCK: usize = 4096;
pub const ENCODABLE_BYTES_PER_BLOB: usize = BLOB_CHUNK_SIZE * ELEMENTS_PER_4844_BLOCK;

#[derive(Derivative, CSAllocatable, CSSelectable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
pub struct BlobChunk<F: SmallField> {
    pub inner: [UInt8<F>; BLOB_CHUNK_SIZE],
}

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct EIP4844OutputData<F: SmallField> {
    pub linear_hash: [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE],
    pub output_hash: [UInt8<F>; keccak256::KECCAK256_DIGEST_SIZE],
}

impl<F: SmallField> CSPlaceholder<F> for EIP4844OutputData<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self {
            linear_hash: [UInt8::<F>::allocate_constant(cs, 0); keccak256::KECCAK256_DIGEST_SIZE],
            output_hash: [UInt8::<F>::allocate_constant(cs, 0); keccak256::KECCAK256_DIGEST_SIZE],
        }
    }
}

pub type EIP4844InputOutput<F> =
    crate::fsm_input_output::ClosedFormInput<F, (), (), EIP4844OutputData<F>>;

pub type EIP4844InputOutputWitness<F> =
    crate::fsm_input_output::ClosedFormInputWitness<F, (), (), EIP4844OutputData<F>>;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct EIP4844CircuitInstanceWitness<F: SmallField> {
    pub closed_form_input: EIP4844InputOutputWitness<F>,
    pub versioned_hash: [u8; 32],
    pub linear_hash_output: [u8; 32],
    pub data_chunks: VecDeque<BlobChunkWitness<F>>,
}
