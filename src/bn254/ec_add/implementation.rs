use super::*;

/// Adds two points in the plain SW projective coordinates.
pub fn projective_add<F, CS>(
    cs: &mut CS,
    point_1: &mut BN256SWProjectivePoint<F>,
    mut point_2: (BN256BaseNNField<F>, BN256BaseNNField<F>),
) -> BN256SWProjectivePoint<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    point_1.add_mixed(cs, &mut point_2)
}
