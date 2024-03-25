use crate::base_structures::recursion_query::RecursionQuery;
use crate::fsm_input_output::commit_variable_length_encodable_item;

use boojum::cs::implementations::prover::ProofConfig;

use boojum::gadgets::recursion::allocated_proof::AllocatedProof;
use boojum::gadgets::recursion::allocated_vk::AllocatedVerificationKey;
use boojum::gadgets::recursion::recursive_transcript::RecursiveTranscript;
use boojum::gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher;

use crate::boojum::cs::gates::PublicInputGate;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::{
    num::Num,
    queue::*,
    traits::{allocatable::CSAllocatable, allocatable::CSAllocatableExt},
};
use std::collections::VecDeque;

use super::*;

pub mod input;

use self::input::*;

use boojum::cs::implementations::verifier::VerificationKeyCircuitGeometry;
use boojum::cs::oracle::TreeHasher;
use boojum::field::FieldExtension;
use boojum::gadgets::recursion::circuit_pow::RecursivePoWRunner;
use boojum::gadgets::recursion::recursive_transcript::CircuitTranscript;
use boojum::gadgets::recursion::recursive_tree_hasher::CircuitTreeHasher;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug(bound = ""))]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct RecursionTipConfig<
    F: SmallField,
    H: TreeHasher<F>,
    EXT: FieldExtension<2, BaseField = F>,
> {
    pub proof_config: ProofConfig,
    pub vk_fixed_parameters: VerificationKeyCircuitGeometry,
    pub _marker: std::marker::PhantomData<(F, H, EXT)>,
}

use boojum::cs::traits::circuit::*;

pub fn recursion_tip_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F> + 'static,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    H: RecursiveTreeHasher<F, Num<F>>,
    EXT: FieldExtension<2, BaseField = F>,
    TR: RecursiveTranscript<
        F,
        CompatibleCap = <H::NonCircuitSimulator as TreeHasher<F>>::Output,
        CircuitReflection = CTR,
    >,
    CTR: CircuitTranscript<
        F,
        CircuitCompatibleCap = <H as CircuitTreeHasher<F, Num<F>>>::CircuitOutput,
        TransciptParameters = TR::TransciptParameters,
    >,
    POW: RecursivePoWRunner<F>,
>(
    cs: &mut CS,
    witness: RecursionTipInstanceWitness<F, H, EXT>,
    round_function: &R,
    config: RecursionTipConfig<F, H::NonCircuitSimulator, EXT>,
    verifier_builder: Box<dyn ErasedBuilderForRecursiveVerifier<F, EXT, CS>>,
    transcript_params: TR::TransciptParameters,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <RecursionQuery<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
{
    let RecursionTipInstanceWitness {
        input,
        vk_witness,
        proof_witnesses,
    } = witness;

    let input = RecursionTipInput::allocate(cs, input);
    let RecursionTipInput {
        node_layer_vk_commitment,
        leaf_layer_parameters,
        branch_circuit_type_set,
        queue_set,
    } = input;

    assert_eq!(config.vk_fixed_parameters, vk_witness.fixed_parameters,);

    let vk = AllocatedVerificationKey::<F, H>::allocate(cs, vk_witness);
    assert_eq!(
        vk.setup_merkle_tree_cap.len(),
        config.vk_fixed_parameters.cap_size
    );
    let _vk_commitment_computed: [_; VK_COMMITMENT_LENGTH] =
        commit_variable_length_encodable_item(cs, &vk, round_function);

    // We expect to see a NODE, and propagate to it

    let RecursionTipConfig {
        proof_config,
        vk_fixed_parameters,
        ..
    } = config;

    let mut proof_witnesses = proof_witnesses;

    assert_eq!(vk_fixed_parameters.parameters, verifier_builder.geometry());
    let verifier = verifier_builder.create_recursive_verifier(cs);

    for (branch_type, initial_queue) in branch_circuit_type_set
        .into_iter()
        .zip(queue_set.into_iter())
    {
        let proof_witness = proof_witnesses.pop_front();

        let proof = AllocatedProof::allocate_from_witness(
            cs,
            proof_witness,
            &verifier,
            &vk_fixed_parameters,
            &proof_config,
        );

        let chunk_is_empty = initial_queue.tail.length.is_zero(cs);
        let chunk_is_meaningful = chunk_is_empty.negated(cs);

        // verify the proof
        let (is_valid, public_inputs) = verifier.verify::<H, TR, CTR, POW>(
            cs,
            transcript_params.clone(),
            &proof,
            &vk_fixed_parameters,
            &proof_config,
            &vk,
        );

        is_valid.conditionally_enforce_true(cs, chunk_is_meaningful);

        use crate::recursion::node_layer::input::RecursionNodeInput;
        let input = RecursionNodeInput {
            branch_circuit_type: branch_type,
            leaf_layer_parameters: leaf_layer_parameters,
            node_layer_vk_commitment: node_layer_vk_commitment,
            queue_state: initial_queue,
        };
        let input_commitment: [_; INPUT_OUTPUT_COMMITMENT_LENGTH] =
            commit_variable_length_encodable_item(cs, &input, round_function);

        assert_eq!(public_inputs.len(), INPUT_OUTPUT_COMMITMENT_LENGTH);
        for (a, b) in input_commitment.iter().zip(public_inputs.into_iter()) {
            Num::conditionally_enforce_equal(cs, chunk_is_meaningful, a, &b);
        }
    }

    let input_commitment: [_; INPUT_OUTPUT_COMMITMENT_LENGTH] =
        commit_variable_length_encodable_item(cs, &input, round_function);
    for el in input_commitment.iter() {
        let gate = PublicInputGate::new(el.get_variable());
        gate.add_to_cs(cs);
    }

    input_commitment
}
