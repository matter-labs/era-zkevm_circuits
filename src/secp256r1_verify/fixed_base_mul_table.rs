use super::secp256r1::fr::Fr;
use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;
use boojum::pairing::ff::{Field, PrimeField};
use boojum::pairing::GenericCurveAffine;
use boojum::pairing::GenericCurveProjective;

const TABLE_NAME: &'static str = "Secp256k1 FIXEDBASEMUL table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Secp256r1FixedBaseMulTable<const U32_WORD_INDEX: usize, const BYTE_OFFSET: usize>;

// Allows for a radix scalar mul by storing all potential exponentiations
// of the generator with 0..255
pub fn create_secp256r1_fixed_base_mul_table<
    F: SmallField,
    const U32_WORD_INDEX: usize,
    const BYTE_OFFSET: usize,
>() -> LookupTable<F, 3> {
    assert!(U32_WORD_INDEX < 8);
    assert!(BYTE_OFFSET < 32);
    let mut content = Vec::with_capacity(1 << 8);
    // point of infinity is encoded as (0,0), and we handle it via select in the multiplication routine
    content.push([F::ZERO, F::ZERO, F::ZERO]);
    let mut base_power = Fr::one();
    for _ in 0..(BYTE_OFFSET * 8) {
        base_power.double();
    }
    let base = Secp256Affine::one();
    let base = base.mul(base_power);
    let mut current = base;
    let base = base.into_affine();
    let repr_word_index = U32_WORD_INDEX / 2;
    let take_low = U32_WORD_INDEX % 2 == 0;
    for a in 1..=u8::MAX {
        let current_affine = current.into_affine();
        let (x, y) = current_affine.as_xy();
        let x_repr_word = x.into_repr().as_ref()[repr_word_index];
        let y_repr_word = y.into_repr().as_ref()[repr_word_index];
        if take_low {
            content.push([
                F::from_u64_unchecked(a as u64),
                F::from_u64_unchecked((x_repr_word as u32) as u64),
                F::from_u64_unchecked((y_repr_word as u32) as u64),
            ]);
        } else {
            content.push([
                F::from_u64_unchecked(a as u64),
                F::from_u64_unchecked(x_repr_word >> 32),
                F::from_u64_unchecked(y_repr_word >> 32),
            ]);
        }
        current.add_assign_mixed(&base);
    }
    assert_eq!(content.len(), 256);
    LookupTable::new_from_content(content, TABLE_NAME.to_string(), 1)
}
