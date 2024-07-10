//! 32-byte implementation of the modular exponentiation algorithm.

use boojum::{
    cs::traits::cs::ConstraintSystem,
    ethereum_types::U256,
    field::SmallField,
    gadgets::{traits::selectable::Selectable, u256::UInt256, u32::UInt32},
};

const U256_MAX_BITS: usize = 256;
const U512_MAX_BITS: usize = 512;
const U256_MAX_LIMBS: usize = 8;
const U512_MAX_LIMBS: usize = 16;

const MAX_BINARY_SEARCH_ITERATIONS: usize = 33;

/// Finds the result of exponentiating `base` to the power of `exponent` modulo `modulus`.
/// Input parameters format is done according to EIP-198:
/// https://eips.ethereum.org/EIPS/eip-198.
///
/// Implementation is based on _Algorithm 1_ from the paper
/// https://cse.buffalo.edu/srds2009/escs2009_submission_Gopal.pdf.
///
/// This implementation works with 32-byte `base`, `exponent`, and `modulus`.
pub fn modexp_32_32_32<F, CS>(
    cs: &mut CS,
    base: &UInt256<F>,
    exponent: &UInt256<F>,
    modulus: &UInt256<F>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut a = UInt256::allocated_constant(cs, U256::one());
    let binary_expansion = exponent
        .to_le_bytes(cs)
        .into_iter()
        .map(|x| x.into_num().spread_into_bits::<CS, 8>(cs))
        .flatten()
        .collect::<Vec<_>>();

    for e in binary_expansion.into_iter().rev() {
        // a <- a^2 mod (modulus)
        let a_squared = a.modmul(cs, &a, modulus);

        // a <- a^2 * (base) mod (modulus)
        let a_base = a_squared.modmul(cs, base, modulus);

        // If the i-th bit of the exponent is 1, then a <- a^2 * (base) mod (modulus)
        // Otherwise, we just set a <- a^2 mod (modulus)
        a = UInt256::conditionally_select(cs, e, &a_base, &a_squared);
    }

    a
}

/// Finds the result of exponentiating `base` to the power of `exponent` modulo `modulus`.
/// Input parameters format is done according to EIP-198:
/// https://eips.ethereum.org/EIPS/eip-198.
///
/// Implementation is based on _Algorithm 1_ from the paper
/// https://cse.buffalo.edu/srds2009/escs2009_submission_Gopal.pdf.
///
/// This implementation works with 32-byte `base` and `modulus` and 4-byte `exponent`.
pub fn modexp_32_4_32<F, CS>(
    cs: &mut CS,
    base: &UInt256<F>,
    exponent: &UInt32<F>,
    modulus: &UInt256<F>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut a = UInt256::allocated_constant(cs, U256::one());
    let binary_expansion = exponent
        .to_le_bytes(cs)
        .into_iter()
        .map(|x| x.into_num().spread_into_bits::<CS, 8>(cs))
        .flatten()
        .collect::<Vec<_>>();

    for e in binary_expansion.into_iter().rev() {
        // a <- a^2 mod (modulus)
        let a_squared = a.modmul(cs, &a, modulus);

        // a <- a^2 * (base) mod (modulus)
        let a_base = a_squared.modmul(cs, base, modulus);

        // If the i-th bit of the exponent is 1, then a <- a^2 * (base) mod (modulus)
        // Otherwise, we just set a <- a^2 mod (modulus)
        a = UInt256::conditionally_select(cs, e, &a_base, &a_squared);
    }

    a
}
