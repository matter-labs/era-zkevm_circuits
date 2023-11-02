use super::*;
use crate::ecrecover::{secp256k1::fr::Fr, Secp256Affine};
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;
use boojum::pairing::ff::PrimeField;
use derivative::*;

const TABLE_NAME: &'static str = "FIXEDBASEMUL table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FixedBaseMulTable<const INDEX: usize, const B: u64>;

// Allows for a radix scalar mul by storing all potential exponentiations
// of the generator with 0..255
pub fn create_fixed_base_mul_table<F: SmallField, const INDEX: usize, const B: u64>(
) -> LookupTable<F, 3> {
    assert!(INDEX < 8);
    assert!(B < 32);
    let mut all_keys = Vec::with_capacity(1 << 8);
    for a in 0..=u8::MAX {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64)];
        all_keys.push(key);
    }
    let mut generator = Secp256Affine::one();
    generator.negate();
    let r = Fr::from_str("256").unwrap();
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();
            let b = r.pow([B]);
            let mut exp = Fr::from_str(&a.to_string()).unwrap();
            exp.mul_assign(&b);
            let result = generator.mul(exp);
            let result = result.into_affine();
            let is_even = INDEX % 2 == 0;
            let res = [result.x, result.y]
                .iter()
                .map(|c| {
                    let index = INDEX / 2;
                    let segment = c.into_repr().0[index];
                    if is_even {
                        F::from_u64_unchecked(segment & (u32::MAX as u64))
                    } else {
                        F::from_u64_unchecked(segment >> 32)
                    }
                })
                .collect::<Vec<F>>();
            smallvec::smallvec![res[0], res[1]]
        },
    )
}
