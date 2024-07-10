use arrayvec::ArrayVec;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::non_native_field::implementations::NonNativeFieldOverU16Params;
use boojum::gadgets::non_native_field::traits::NonNativeField;
use boojum::gadgets::u256::UInt256;
use std::sync::Arc;

use crate::bn254::{BN256BaseNNField, BN256BaseNNFieldParams, BN256Fq, BN256Fq2NNField};
use crate::ethereum_types::U256;
use boojum::pairing::ff::PrimeField;

// The Short Weierstrass equation of the curve is  y^2 = x^3 + B.
// B parameter for BN256 curve equation.
const B: &str = "3";
const B_TWIST_C0: &str =
    "19485874751759354771024239261021720505790618469301721065564631296452457478373";
const B_TWIST_C1: &str =
    "266929791119991161246907387137283842545076965332900288569378510910307636690";

/// Checks that each passed value is in `BN256` primary field:
/// base or scalar depending on params.
/// Masks value in-place otherwise.
pub(crate) fn validate_in_field<
    F: SmallField,
    T: PrimeField,
    CS: ConstraintSystem<F>,
    const N: usize,
>(
    cs: &mut CS,
    values: &mut [&mut UInt256<F>; N],
    params: &Arc<NonNativeFieldOverU16Params<T, 17>>,
) -> ArrayVec<Boolean<F>, N> {
    let p_u256 = U256([
        params.modulus_u1024.as_ref().as_words()[0],
        params.modulus_u1024.as_ref().as_words()[1],
        params.modulus_u1024.as_ref().as_words()[2],
        params.modulus_u1024.as_ref().as_words()[3],
    ]);
    let p_u256 = UInt256::allocated_constant(cs, p_u256);

    let mut exceptions = ArrayVec::<_, N>::new();

    for value in values.iter_mut() {
        let (_, is_in_range) = value.overflowing_sub(cs, &p_u256);
        **value = value.mask(cs, is_in_range);
        let is_not_in_range = is_in_range.negated(cs);
        exceptions.push(is_not_in_range);
    }

    exceptions
}

/// Checks that the passed point is on `BN256` curve.
/// The `Infinity` point is not counted as on curve.
pub(crate) fn is_on_curve<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    point: (&BN256BaseNNField<F>, &BN256BaseNNField<F>),
    params: &Arc<BN256BaseNNFieldParams>,
) -> Boolean<F> {
    let (x, y) = point;

    let mut x = x.clone();
    let mut y = y.clone();

    let b = BN256Fq::from_str(B).unwrap();
    let mut b = BN256BaseNNField::allocated_constant(cs, b, params);

    let mut x_squared = x.square(cs);
    let mut x_cubed = x_squared.mul(cs, &mut x);

    let mut x_cubed_plus_b = x_cubed.add(cs, &mut b);
    let mut y_squared = y.square(cs);

    BN256BaseNNField::equals(cs, &mut y_squared, &mut x_cubed_plus_b)
}

/// Checks that the passed point is on G2 `BN256` curve.
/// The `Infinity` point is not counted as on curve.
/// See https://hackmd.io/@jpw/bn254#Twists for further details.
pub(crate) fn is_on_twist_curve<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    point: (&BN256Fq2NNField<F>, &BN256Fq2NNField<F>),
    params: &Arc<BN256BaseNNFieldParams>,
) -> Boolean<F> {
    let (x, y) = point;

    let mut x = x.clone();
    let mut y = y.clone();

    let b_c0 = BN256Fq::from_str(B_TWIST_C0).unwrap();
    let b_c1 = BN256Fq::from_str(B_TWIST_C1).unwrap();

    let b_c0 = BN256BaseNNField::allocated_constant(cs, b_c0, params);
    let b_c1 = BN256BaseNNField::allocated_constant(cs, b_c1, params);

    let mut b = BN256Fq2NNField::new(b_c0, b_c1);

    let mut x_squared = x.square(cs);
    let mut x_cubed = x_squared.mul(cs, &mut x);

    let mut x_cubed_plus_b = x_cubed.add(cs, &mut b);
    let mut y_squared = y.square(cs);

    y_squared.equals(cs, &mut x_cubed_plus_b)
}

/// Check whether passed point is classified as `Infinity`.
/// See https://eips.ethereum.org/EIPS/eip-196 for further details.
// We use `UInt256` instead of `BN256BaseNNField`
// because we need to be able to check the unmasked value.
pub(crate) fn is_affine_infinity<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    point: (&UInt256<F>, &UInt256<F>),
) -> Boolean<F> {
    let (x, y) = point;
    let x_is_zero = x.is_zero(cs);
    let y_is_zero = y.is_zero(cs);

    x_is_zero.and(cs, y_is_zero)
}

/// Check whether passed point in G2 is classified as `Infinity`.
/// See https://eips.ethereum.org/EIPS/eip-196 for further details.
// We use `UInt256` instead of `BN256BaseNNField`
// because we need to be able to check the unmasked value.
pub(crate) fn is_twist_affine_infinity<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    point: (&UInt256<F>, &UInt256<F>, &UInt256<F>, &UInt256<F>),
) -> Boolean<F> {
    let (x_c0, x_c1, y_c0, y_c1) = point;

    let x_c0_is_zero = x_c0.is_zero(cs);
    let x_c1_is_zero = x_c1.is_zero(cs);
    let y_c0_is_zero = y_c0.is_zero(cs);
    let y_c1_is_zero = y_c1.is_zero(cs);

    Boolean::multi_and(
        cs,
        &[x_c0_is_zero, x_c1_is_zero, y_c0_is_zero, y_c1_is_zero],
    )
}
