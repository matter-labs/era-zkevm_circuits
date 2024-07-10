//! 256-byte implementation of the modular exponentiation algorithm.

use boojum::{
    crypto_bigint::U1024,
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{traits::selectable::Selectable, u2048::UInt2048, u32::UInt32},
};

const U2048_MAX_BITS: usize = 2048;
const U4096_MAX_BITS: usize = 4096;
const U2048_MAX_LIMBS: usize = 64;
const U4096_MAX_LIMBS: usize = 128;

/// Finds the result of exponentiating `base` to the power of `exponent` modulo `modulus`.
/// Input parameters format is done according to EIP-198:
/// https://eips.ethereum.org/EIPS/eip-198.
///
/// Implementation is based on _Algorithm 1_ from the paper
/// https://cse.buffalo.edu/srds2009/escs2009_submission_Gopal.pdf.
///
/// This implementation works with 256-byte `base`, `exponent`, and `modulus`.
pub fn modexp_256_256_256<F, CS>(
    cs: &mut CS,
    base: &UInt2048<F>,
    exponent: &UInt2048<F>,
    modulus: &UInt2048<F>,
) -> UInt2048<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut a = UInt2048::allocated_constant(cs, (U1024::ONE, U1024::ZERO));
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
        a = UInt2048::conditionally_select(cs, e, &a_base, &a_squared);
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
/// This implementation works with 256-byte `base`, `modulus`, and 8-byte `exponent`.
/// Since `UInt64<F>` is not implemented yet as of now,
/// we use two [`UInt32<F>`]s (low and high, respectively) to represent the exponent.
pub fn modexp_256_8_256<F, CS>(
    cs: &mut CS,
    base: &UInt2048<F>,
    exponent: &(UInt32<F>, UInt32<F>),
    modulus: &UInt2048<F>,
) -> UInt2048<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Helper function to convert a UInt32<F> into a binary expansion
    let mut into_binary_expansion = |x: &UInt32<F>| {
        x.to_le_bytes(cs)
            .into_iter()
            .map(|x| x.into_num().spread_into_bits::<CS, 8>(cs))
            .flatten()
            .collect::<Vec<_>>()
    };

    // Convert the exponent into a binary expansion. We do that by concatenating
    // the high part binary expansion with the low part binary expansion.
    let (low, high) = exponent;
    let mut binary_expansion = into_binary_expansion(high);
    let mut low_binary_expansion = into_binary_expansion(low);
    binary_expansion.append(&mut low_binary_expansion);

    // Start the modular exponentiation
    let mut a = UInt2048::allocated_constant(cs, (U1024::ONE, U1024::ZERO));
    for e in binary_expansion.into_iter().rev() {
        // a <- a^2 mod (modulus)
        let a_squared = a.modmul(cs, &a, modulus);

        // a <- a^2 * (base) mod (modulus)
        let a_base = a_squared.modmul(cs, base, modulus);

        // If the i-th bit of the exponent is 1, then a <- a^2 * (base) mod (modulus)
        // Otherwise, we just set a <- a^2 mod (modulus)
        a = UInt2048::conditionally_select(cs, e, &a_base, &a_squared);
    }

    a
}
