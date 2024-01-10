use crate::base_structures::state_diff_record::StateDiffRecord;
use crate::demux_log_queue::StorageLogQueue;
use crate::ethereum_types::U256;
use crate::fsm_input_output::circuit_inputs::INPUT_OUTPUT_COMMITMENT_LENGTH;
use crate::keccak256_round_function::keccak256_absorb_and_run_permutation;
use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::config::*;
use boojum::crypto_bigint::{Zero, U1024};
use boojum::cs::gates::ConstantAllocatableCS;
use boojum::cs::traits::cs::{ConstraintSystem, DstBuffer};
use boojum::cs::{Place, Variable};
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::keccak256;
use boojum::gadgets::non_native_field::implementations::*;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::CircuitQueue;
use boojum::gadgets::queue::CircuitQueueWitness;
use boojum::gadgets::queue::QueueState;
use boojum::gadgets::traits::allocatable::{CSAllocatable, CSAllocatableExt, CSPlaceholder};
use boojum::gadgets::traits::castable::WitnessCastable;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::gadgets::u16::UInt16;
use boojum::gadgets::u256::UInt256;
use boojum::gadgets::u32::UInt32;
use boojum::gadgets::u8::UInt8;
use boojum::pairing::ff::{Field, PrimeField};
use std::mem::MaybeUninit;
use std::sync::{Arc, RwLock};

use super::*;

pub mod input;
use self::input::*;

use boojum::pairing::bls12_381::fr::Fr as Bls12_381Fr;

const NUM_WORDS_FR: usize = 17;
type Bls12_381ScalarNNFieldParams = NonNativeFieldOverU16Params<Bls12_381Fr, NUM_WORDS_FR>;
type Bls12_381ScalarNNField<F> = NonNativeFieldOverU16<F, Bls12_381Fr, 17>;

// turns 128 bits into a Bls12 field element.
fn convert_truncated_keccak_digest_to_field_element<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: [UInt8<F>; 16],
    params: &Arc<Bls12_381ScalarNNFieldParams>,
) -> Bls12_381ScalarNNField<F> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; NUM_WORDS_FR];
    // since the value would be interpreted as big endian in the L1 we need to reverse our bytes to
    // get the correct value
    for (dst, src) in limbs.iter_mut().zip(input.array_chunks::<2>().rev()) {
        let [c0, c1] = *src;
        // for some reason there is no "from_be_bytes"
        *dst = UInt16::from_le_bytes(cs, [c1, c0]).get_variable();
    }

    // Note: we do not need to check for overflows because the max value is 2^128 which is less
    // than the field modulus.
    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 1 },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    }
}

// here we just interpret it as LE
fn convert_blob_chunk_to_field_element<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: [UInt8<F>; BLOB_CHUNK_SIZE],
    params: &Arc<Bls12_381ScalarNNFieldParams>,
) -> Bls12_381ScalarNNField<F> {
    // compose the bytes into u16 words for the nonnative wrapper
    let zero_var = cs.allocate_constant(F::ZERO);
    let mut limbs = [zero_var; NUM_WORDS_FR];
    let input_chunks = input.array_chunks::<2>();
    let remainder = input_chunks.remainder();
    for (dst, src) in limbs.iter_mut().zip(input_chunks) {
        *dst = UInt16::from_le_bytes(cs, *src).get_variable();
    }

    // since array_chunks drops any remaining elements that don't fit in the size requirement,
    // we need to manually set the last byte in limbs
    limbs[15] = remainder[0].get_variable();

    // Note: we do not need to check for overflows because the max value is 2^248 which is less
    // than the field modulus.
    NonNativeFieldOverU16 {
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses: 1 },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    }
}

/// We interpret out pubdata as chunks of 31 bytes, that are coefficients of
/// some polynomial, starting from the highest one. It's different from 4844 blob data format,
/// and we provide additional functions to compute the corresponding 4844 blob data, and restore back
pub fn eip_4844_entry_point<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
>(
    cs: &mut CS,
    witness: EIP4844CircuitInstanceWitness<F>,
    round_function: &R,
    params: usize,
) -> [Num<F>; INPUT_OUTPUT_COMMITMENT_LENGTH]
where
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    [(); <UInt256<F> as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN + 1]:,
{
    let limit = params;

    assert_eq!(limit, ELEMENTS_PER_4844_BLOCK); // max blob length eip4844

    let EIP4844CircuitInstanceWitness {
        closed_form_input,
        versioned_hash,
        linear_hash_output,
        data_chunks,
    } = witness;

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        assert_eq!(data_chunks.len(), ELEMENTS_PER_4844_BLOCK)
    }

    let mut data_chunks = data_chunks;
    let zero_u8 = UInt8::zero(cs);

    let versioned_hash = <[UInt8<F>; 32]>::allocate(cs, versioned_hash);
    let linear_hash_output = <[UInt8<F>; 32]>::allocate(cs, linear_hash_output);

    let boolean_true = Boolean::allocated_constant(cs, true);
    let mut structured_input = EIP4844InputOutput::<F> {
        start_flag: boolean_true,
        completion_flag: boolean_true,
        observable_input: (),
        observable_output: EIP4844OutputData {
            linear_hash: [UInt8::<F>::zero(cs); keccak256::KECCAK256_DIGEST_SIZE],
            output_hash: [UInt8::<F>::zero(cs); keccak256::KECCAK256_DIGEST_SIZE],
        },
        hidden_fsm_input: (),
        hidden_fsm_output: (),
    };

    // create a field element out of the hash of the input hash and the kzg commitment
    let challenge_hash = boojum::gadgets::keccak256::keccak256(
        cs,
        linear_hash_output
            .into_iter()
            .chain(versioned_hash.into_iter())
            .collect::<Vec<UInt8<F>>>()
            .as_slice(),
    );

    // truncate hash to 128 bits
    // NOTE: it is safe to draw a random scalar at max 128 bits because of the schwartz zippel
    // lemma
    let mut truncated_hash = [zero_u8; 16];
    // take last 16 bytes to get max 2^128
    // in big endian scenario
    truncated_hash.copy_from_slice(&challenge_hash[16..]);
    let params = Arc::new(Bls12_381ScalarNNFieldParams::create());
    let mut evaluation_point =
        convert_truncated_keccak_digest_to_field_element(cs, truncated_hash, &params);

    let mut buffer = Vec::with_capacity(31 * 4096);

    let mut opening_value =
        Bls12_381ScalarNNField::<F>::allocated_constant(cs, Bls12_381Fr::zero(), &params);

    // We always pad the pubdata to be 31*(2^12) bytes, no matter how many elements we fill.
    // Therefore, we can run the circuit straightforwardly without needing to account for potential
    // changes in the cycle number in which the padding happens. Hence, we run the loop
    // to perform the horner's rule evaluation of the blob polynomial and then finalize the hash
    // out of the loop with a single keccak256 call.
    for cycle in 0..limit {
        let el = data_chunks
            .pop_front()
            .unwrap_or(BlobChunk::placeholder_witness());
        let el = BlobChunk::<F>::allocate(cs, el);
        // polynomial evaluations via horner's rule
        let mut fe = convert_blob_chunk_to_field_element(cs, el.inner, &params);
        // horner's rule is defined as evaluating a polynomial a_0 + a_1x + a_2x^2 + ... + a_nx^n
        // in the form of a_0 + x(a_1 + x(a_2 + x(a_3 + ... + x(a_{n-1} + xa_n))))
        // since the blob is considered to be a polynomial in lagrange form, we essentially
        // 'work backwards' and start with the highest degree coefficients first. so we can
        // add and multiply and at the last step we only add the coefficient.
        opening_value = opening_value.add(cs, &mut fe);
        if cycle != limit - 1 {
            opening_value = opening_value.mul(cs, &mut evaluation_point);
        }

        buffer.extend(el.inner);
    }

    use boojum::gadgets::keccak256::keccak256;
    let keccak256_hash = keccak256(cs, &buffer);

    // hash equality check
    for (input_byte, hash_byte) in linear_hash_output.iter().zip(keccak256_hash) {
        Num::enforce_equal(cs, &input_byte.into_num(), &hash_byte.into_num());
    }

    // now commit to versioned hash || opening point || openinig value

    // normalize and serialize opening value as BE
    let mut opening_value_be_bytes = [zero_u8; 32];
    opening_value.normalize(cs);

    for (dst, src) in opening_value_be_bytes
        .array_chunks_mut::<2>()
        .zip(opening_value.limbs[..16].iter().rev())
    {
        // field element is normalized, so all limbs are 16 bits
        let be_bytes = unsafe { UInt16::from_variable_unchecked(*src).to_be_bytes(cs) };
        *dst = be_bytes;
    }

    let output_hash = keccak256(
        cs,
        versioned_hash
            .into_iter()
            .chain(truncated_hash.into_iter())
            .chain(opening_value_be_bytes.into_iter())
            .collect::<Vec<UInt8<F>>>()
            .as_slice(),
    );

    let mut observable_output = EIP4844OutputData::placeholder(cs);
    observable_output.linear_hash = keccak256_hash;
    observable_output.output_hash = output_hash;
    structured_input.observable_output = observable_output;

    // self-check
    structured_input.hook_compare_witness(cs, &closed_form_input);

    use crate::fsm_input_output::commit_variable_length_encodable_item;
    use crate::fsm_input_output::ClosedFormInputCompactForm;
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

fn omega() -> Bls12_381Fr {
    let mut omega = Bls12_381Fr::root_of_unity();
    let exp = ELEMENTS_PER_4844_BLOCK.trailing_zeros();

    for _ in exp..Bls12_381Fr::S {
        omega.square();
    }

    omega
}

fn omega_inv() -> Bls12_381Fr {
    omega().inverse().unwrap()
}

fn m_inv() -> Bls12_381Fr {
    Bls12_381Fr::from_str(&format!("{}", ELEMENTS_PER_4844_BLOCK))
        .unwrap()
        .inverse()
        .unwrap()
}

fn bitreverse_idx(mut n: u32, l: u32) -> u32 {
    let mut r = 0;
    for _ in 0..l {
        r = (r << 1) | (n & 1);
        n >>= 1;
    }

    r
}

fn bitreverse<T>(a: &mut [T]) {
    let n = a.len() as u32;
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros();

    for k in 0..n {
        let rk = bitreverse_idx(k, log_n);
        if k < rk {
            a.swap(rk as usize, k as usize);
        }
    }
}

fn serial_fft(a: &mut [Bls12_381Fr], omega: &Bls12_381Fr, log_n: u32) {
    let n = a.len() as u32;
    assert_eq!(n, 1 << log_n);

    bitreverse(a);

    let mut m = 1;
    for _ in 0..log_n {
        let w_m = omega.pow(&[(n / (2 * m)) as u64]);

        let mut k = 0;
        while k < n {
            let mut w = Bls12_381Fr::one();
            for j in 0..m {
                let mut t = a[(k + j + m) as usize];
                t.mul_assign(&w);
                let mut tmp = a[(k + j) as usize];
                tmp.sub_assign(&t);
                a[(k + j + m) as usize] = tmp;
                a[(k + j) as usize].add_assign(&t);
                w.mul_assign(&w_m);
            }

            k += 2 * m;
        }

        m *= 2;
    }
}

fn fft(a: &mut [Bls12_381Fr]) {
    serial_fft(a, &omega(), ELEMENTS_PER_4844_BLOCK.trailing_zeros());
}

fn ifft(a: &mut [Bls12_381Fr]) {
    serial_fft(a, &omega_inv(), ELEMENTS_PER_4844_BLOCK.trailing_zeros());
    let m_inv = m_inv();
    for a in a.iter_mut() {
        a.mul_assign(&m_inv);
    }
}

pub fn zksync_pubdata_into_ethereum_4844_data(input: &[u8]) -> Vec<u8> {
    let mut poly = zksync_pubdata_into_monomial_form_poly(input);
    fft(&mut poly);
    // and we need to bitreverse
    bitreverse(&mut poly);
    // and now serialize in BE form as Ethereum expects
    let mut result = Vec::with_capacity(32 * ELEMENTS_PER_4844_BLOCK);
    use boojum::pairing::ff::PrimeFieldRepr;
    for el in poly.into_iter() {
        let mut buffer = [0u8; 32];
        el.into_repr().write_be(&mut buffer[..]).unwrap();
        result.extend(buffer);
    }

    result
}

pub fn zksync_pubdata_into_monomial_form_poly(input: &[u8]) -> Vec<Bls12_381Fr> {
    assert_eq!(input.len(), BLOB_CHUNK_SIZE * ELEMENTS_PER_4844_BLOCK);
    // we interpret it as coefficients starting from the top one
    let mut poly = Vec::with_capacity(ELEMENTS_PER_4844_BLOCK);
    use boojum::pairing::ff::PrimeFieldRepr;
    for bytes in input.array_chunks::<BLOB_CHUNK_SIZE>().rev() {
        let mut buffer = [0u8; 32];
        buffer[..BLOB_CHUNK_SIZE].copy_from_slice(bytes);
        let mut repr = <Bls12_381Fr as boojum::pairing::ff::PrimeField>::Repr::default();
        repr.read_le(&buffer[..]).unwrap();
        let as_field_element = Bls12_381Fr::from_repr(repr).unwrap();
        poly.push(as_field_element);
    }

    poly
}

pub fn ethereum_4844_pubdata_into_bitreversed_lagrange_form_poly(input: &[u8]) -> Vec<Bls12_381Fr> {
    assert_eq!(input.len(), 32 * ELEMENTS_PER_4844_BLOCK);
    let mut poly = Vec::with_capacity(ELEMENTS_PER_4844_BLOCK);
    use boojum::pairing::ff::PrimeFieldRepr;
    for bytes in input.array_chunks::<32>().rev() {
        let mut repr = <Bls12_381Fr as boojum::pairing::ff::PrimeField>::Repr::default();
        repr.read_be(&bytes[..]).unwrap();
        let as_field_element = Bls12_381Fr::from_repr(repr).unwrap();
        poly.push(as_field_element);
    }

    poly
}

pub fn ethereum_4844_data_into_zksync_pubdata(input: &[u8]) -> Vec<u8> {
    assert_eq!(input.len(), 32 * ELEMENTS_PER_4844_BLOCK);
    let mut poly = ethereum_4844_pubdata_into_bitreversed_lagrange_form_poly(input);
    // and we need to bitreverse
    bitreverse(&mut poly);
    // now we need to iFFT it to get monomial form
    ifft(&mut poly);
    // and now serialize in LE by BLOB_CHUNK_SIZE chunks
    let mut result = Vec::with_capacity(BLOB_CHUNK_SIZE * ELEMENTS_PER_4844_BLOCK);
    use boojum::pairing::ff::PrimeFieldRepr;
    for el in poly.into_iter() {
        let mut buffer = [0u8; 32];
        el.into_repr().write_le(&mut buffer[..]).unwrap();
        result.extend_from_slice(&buffer[..BLOB_CHUNK_SIZE]);
    }

    result
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::*;
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::*;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::CSGeometry;
    use boojum::cs::*;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::field::traits::field_like::PrimeFieldLike;
    use boojum::field::Field;
    use boojum::field::SmallField;
    use boojum::gadgets::queue::CircuitQueueRawWitness;
    use boojum::gadgets::tables::byte_split::ByteSplitTable;
    use boojum::gadgets::tables::*;
    use boojum::implementations::poseidon2::Poseidon2Goldilocks;
    use boojum::pairing::bls12_381::G1;
    use boojum::pairing::ff::PrimeFieldRepr;
    use boojum::pairing::ff::{Field as PairingField, PrimeField, SqrtField};
    use boojum::worker::Worker;
    use rand::SeedableRng;
    use rand::{Rand, Rng};

    type F = GoldilocksField;
    type P = GoldilocksField;

    #[test]
    fn test_eip4844() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
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
                    num_repetitions: 20,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = PublicInputGate::configure_builder(
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
            // let owned_cs = ReductionGate::<F, 4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 8, share_constants: true });
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
            let builder = DotProductGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // let owned_cs = DotProductGate::<4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 1, share_constants: true });
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl = CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(
            geometry,
            max_variables,
            max_trace_len,
        );
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(());

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let cs = &mut owned_cs;

        let round_function = Poseidon2Goldilocks;

        // make some random chunks
        let mut data_chunks = vec![[0u8; BLOB_CHUNK_SIZE]; ELEMENTS_PER_4844_BLOCK];
        let mut rng = rand::XorShiftRng::from_seed([0, 0, 0, 42]);
        for dst in data_chunks.iter_mut() {
            let el = Bls12_381Fr::rand(&mut rng);
            let mut bytes = [0u8; 32];
            el.into_repr().write_le(&mut bytes[..]).unwrap();
            dst.copy_from_slice(&bytes[..BLOB_CHUNK_SIZE]);
        }

        let mut blob_data_flattened = vec![];
        for el in data_chunks.iter() {
            blob_data_flattened.extend_from_slice(el);
        }

        // now we can get it as polynomial, and
        use zkevm_opcode_defs::sha3::*;
        let mut linear_hash_output = [0u8; 32];
        let digest = Keccak256::digest(&blob_data_flattened);

        linear_hash_output.copy_from_slice(digest.as_slice());

        // now we can get some quasi-setup for KZG and make a blob
        let poly = zksync_pubdata_into_monomial_form_poly(&blob_data_flattened);

        let mut setup = Vec::with_capacity(ELEMENTS_PER_4844_BLOCK);
        use boojum::pairing::CurveAffine;
        use boojum::pairing::CurveProjective;
        let mut point = G1::one();
        let scalar = Bls12_381Fr::from_str("42").unwrap().into_repr();
        for _ in 0..ELEMENTS_PER_4844_BLOCK {
            setup.push(point);
            point.mul_assign(scalar);
        }

        // compute commitment
        let mut commitment = G1::zero();
        for (scalar, point) in poly.iter().zip(setup.iter()) {
            let mut el = *point;
            el.mul_assign(scalar.into_repr());
            commitment.add_assign(&el);
        }

        let (kzg_commitment_x, kzg_commitment_y) = commitment.into_affine().into_xy_unchecked();
        let mut buffer = [0u8; 96];
        kzg_commitment_x
            .into_repr()
            .write_be(&mut buffer[..48])
            .unwrap();
        kzg_commitment_y
            .into_repr()
            .write_be(&mut buffer[48..])
            .unwrap();

        let mut versioned_hash = [0u8; 32];
        let digest = Keccak256::digest(&buffer);
        versioned_hash.copy_from_slice(digest.as_slice());
        versioned_hash[0] = 0x01;

        let evaluation_point = Keccak256::digest(
            linear_hash_output
                .into_iter()
                .chain(versioned_hash.into_iter())
                .collect::<Vec<u8>>(),
        )[16..]
            .to_vec();

        dbg!(hex::encode(&evaluation_point));

        let mut buffer = [0u8; 32];
        buffer[16..].copy_from_slice(&evaluation_point);
        let mut evaluation_point_repr =
            <Bls12_381Fr as boojum::pairing::ff::PrimeField>::Repr::default();
        evaluation_point_repr.read_be(&buffer[..]).unwrap();
        let evaluation_point_fr = Bls12_381Fr::from_repr(evaluation_point_repr).unwrap();
        dbg!(evaluation_point_fr);

        use boojum::pairing::bls12_381::FrRepr;
        // evaluate polynomial
        let mut evaluation_result = Bls12_381Fr::zero();
        let mut power = Bls12_381Fr::one();
        for coeff in poly.iter() {
            let mut tmp = *coeff;
            tmp.mul_assign(&power);
            evaluation_result.add_assign(&tmp);
            power.mul_assign(&evaluation_point_fr);
        }

        dbg!(evaluation_result);
        let mut opening_value_bytes = [0u8; 32];
        evaluation_result
            .into_repr()
            .write_be(&mut opening_value_bytes[..])
            .unwrap();

        let mut observable_output = EIP4844OutputData::<F>::placeholder_witness();
        let output_hash = Keccak256::digest(
            versioned_hash
                .into_iter()
                .chain(evaluation_point.into_iter())
                .chain(opening_value_bytes.into_iter())
                .collect::<Vec<u8>>(),
        )
        .into();
        dbg!(hex::encode(&output_hash));
        observable_output.output_hash = output_hash;
        observable_output.linear_hash = linear_hash_output;

        let closed_form_input = EIP4844InputOutputWitness {
            start_flag: true,
            completion_flag: true,
            observable_input: (),
            observable_output: observable_output,
            hidden_fsm_input: (),
            hidden_fsm_output: (),
        };

        let witness = EIP4844CircuitInstanceWitness {
            closed_form_input,
            versioned_hash,
            linear_hash_output,
            data_chunks: data_chunks
                .into_iter()
                .map(|el| BlobChunkWitness { inner: el })
                .collect::<VecDeque<BlobChunkWitness<F>>>(),
        };

        eip_4844_entry_point::<_, _, _>(cs, witness, &round_function, 4096);

        dbg!(cs.next_available_row());

        cs.pad_and_shrink();

        let mut cs = owned_cs.into_assembly();
        cs.print_gate_stats();
        let worker = Worker::new();
        assert!(cs.check_if_satisfied(&worker));
    }
}
