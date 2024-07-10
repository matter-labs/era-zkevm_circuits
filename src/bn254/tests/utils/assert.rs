use crate::bn254::{
    BN256Affine, BN256Fq12NNField, BN256Fq2NNField, BN256Fq6NNField, BN256SWProjectivePoint,
    BN256SWProjectivePointTwisted,
};
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::goldilocks::GoldilocksField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::pairing::bn256::G2Affine;
use boojum::pairing::CurveAffine;

type F = GoldilocksField;

pub(in super::super) fn assert_equal_g1_points<CS>(
    cs: &mut CS,
    point: &mut BN256SWProjectivePoint<F>,
    expected: &mut BN256SWProjectivePoint<F>,
) where
    CS: ConstraintSystem<F>,
{
    // Converting to affine representation
    let default_point = BN256Affine::one();
    let ((x1, y1), is_infty1) = point.convert_to_affine_or_default(cs, default_point);
    let ((x2, y2), is_infty2) = expected.convert_to_affine_or_default(cs, default_point);

    // Enforcing point not to be at infinity
    let boolean_false = Boolean::allocated_constant(cs, false);
    Boolean::enforce_equal(cs, &is_infty1, &boolean_false);
    Boolean::enforce_equal(cs, &is_infty2, &boolean_false);

    // Enforcing x coordinates to be equal
    let x1 = x1.witness_hook(cs)().unwrap().get();
    let x2 = x2.witness_hook(cs)().unwrap().get();
    assert_eq!(x1, x2, "x coordinates are not equal");

    // Enforcing y coordinates to be equal
    let y1 = y1.witness_hook(cs)().unwrap().get();
    let y2 = y2.witness_hook(cs)().unwrap().get();
    assert_eq!(y1, y2, "y coordinates are not equal");
}

pub(in super::super) fn assert_equal_g2_points<CS>(
    cs: &mut CS,
    point: &mut BN256SWProjectivePointTwisted<F>,
    expected: &mut BN256SWProjectivePointTwisted<F>,
) where
    CS: ConstraintSystem<F>,
{
    // Converting to affine representation
    let default_point = G2Affine::one();
    let ((x1, y1), is_infty1) = point.convert_to_affine_or_default(cs, default_point);
    let ((x2, y2), is_infty2) = expected.convert_to_affine_or_default(cs, default_point);

    // Enforcing point not to be at infinity
    let boolean_false = Boolean::allocated_constant(cs, false);
    Boolean::enforce_equal(cs, &is_infty1, &boolean_false);
    Boolean::enforce_equal(cs, &is_infty2, &boolean_false);

    // Enforcing x coordinates to be equal
    let x1_c0 = x1.witness_hook(cs)().unwrap().0.get();
    let x1_c1 = x1.witness_hook(cs)().unwrap().1.get();
    let x2_c0 = x2.witness_hook(cs)().unwrap().0.get();
    let x2_c1 = x2.witness_hook(cs)().unwrap().1.get();
    assert!(
        x1_c0 == x2_c0 && x1_c1 == x2_c1,
        "x coordinates are not equal"
    );

    // Enforcing y coordinates to be equal
    let y1_c0 = y1.witness_hook(cs)().unwrap().0.get();
    let y1_c1 = y1.witness_hook(cs)().unwrap().1.get();
    let y2_c0 = y2.witness_hook(cs)().unwrap().0.get();
    let y2_c1 = y2.witness_hook(cs)().unwrap().1.get();
    assert!(
        y1_c0 == y2_c0 && y1_c1 == y2_c1,
        "y coordinates are not equal"
    );
}

pub(in super::super) fn assert_equal_g2_jacobian_points<CS>(
    cs: &mut CS,
    point: &mut BN256SWProjectivePointTwisted<F>,
    expected: &mut BN256SWProjectivePointTwisted<F>,
) where
    CS: ConstraintSystem<F>,
{
    // Converting to affine representation via Jacobian coordinates
    let default_point = G2Affine::one();
    let ((x1, y1), is_infty1) = point.convert_to_affine_jacobian(cs, default_point);
    let ((x2, y2), is_infty2) = expected.convert_to_affine_jacobian(cs, default_point);

    // Enforcing point not to be at infinity
    let boolean_false = Boolean::allocated_constant(cs, false);
    Boolean::enforce_equal(cs, &is_infty1, &boolean_false);
    Boolean::enforce_equal(cs, &is_infty2, &boolean_false);

    // Enforcing x coordinates to be equal
    let x1_c0 = x1.witness_hook(cs)().unwrap().0.get();
    let x1_c1 = x1.witness_hook(cs)().unwrap().1.get();
    let x2_c0 = x2.witness_hook(cs)().unwrap().0.get();
    let x2_c1 = x2.witness_hook(cs)().unwrap().1.get();
    assert!(
        x1_c0 == x2_c0 && x1_c1 == x2_c1,
        "x coordinates are not equal"
    );

    // Enforcing y coordinates to be equal
    let y1_c0 = y1.witness_hook(cs)().unwrap().0.get();
    let y1_c1 = y1.witness_hook(cs)().unwrap().1.get();
    let y2_c0 = y2.witness_hook(cs)().unwrap().0.get();
    let y2_c1 = y2.witness_hook(cs)().unwrap().1.get();
    assert!(
        y1_c0 == y2_c0 && y1_c1 == y2_c1,
        "y coordinates are not equal"
    );
}

fn equal_fq2<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq2NNField<F>,
    b: &BN256Fq2NNField<F>,
) -> bool {
    let a_c0 = a.c0.witness_hook(cs)().unwrap().get();
    let a_c1 = a.c1.witness_hook(cs)().unwrap().get();

    let b_c0 = b.c0.witness_hook(cs)().unwrap().get();
    let b_c1 = b.c1.witness_hook(cs)().unwrap().get();

    a_c0.eq(&b_c0) && a_c1.eq(&b_c1)
}

fn equal_fq6<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq6NNField<F>,
    b: &BN256Fq6NNField<F>,
) -> bool {
    equal_fq2(cs, &a.c0, &b.c0) && equal_fq2(cs, &a.c1, &b.c1) && equal_fq2(cs, &a.c2, &b.c2)
}

fn equal_fq12<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq12NNField<F>,
    b: &BN256Fq12NNField<F>,
) -> bool {
    equal_fq6(cs, &a.c0, &b.c0) && equal_fq6(cs, &a.c1, &b.c1)
}

pub(in super::super) fn assert_equal_fq2<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq2NNField<F>,
    b: &BN256Fq2NNField<F>,
) {
    assert!(equal_fq2(cs, a, b));
}

pub(in super::super) fn assert_equal_fq6<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq6NNField<F>,
    b: &BN256Fq6NNField<F>,
) {
    assert!(equal_fq6(cs, a, b));
}

pub(in super::super) fn assert_equal_fq12<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq12NNField<F>,
    b: &BN256Fq12NNField<F>,
) {
    assert!(equal_fq12(cs, a, b));
}

pub(in super::super) fn assert_not_equal_fq12<CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &BN256Fq12NNField<F>,
    b: &BN256Fq12NNField<F>,
) {
    assert!(!equal_fq12(cs, a, b));
}
