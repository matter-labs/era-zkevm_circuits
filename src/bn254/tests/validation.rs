pub mod test {
    use std::sync::Arc;

    use crate::bn254::tests::utils::cs::create_test_cs;
    use crate::bn254::{
        bn254_base_field_params, validation, BN256BaseNNField, BN256Fq2NNField, BN256SWProjectivePoint, BN256SWProjectivePointTwisted
    };
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::boolean::Boolean;
    use boojum::gadgets::non_native_field::traits::NonNativeField;
    use boojum::pairing::bn256::{Fq, G1Affine, G2Affine};
    use boojum::pairing::ff::Field;
    use boojum::pairing::CurveAffine;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Tests whether when inserted a valid point on the regular curve, 
    /// the validation function returns true.
    #[test]
    fn test_on_curve_validation_valid() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 20);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();

        // Preparing booleans
        let boolean_true = Boolean::allocated_constant(cs, true);
        let boolean_false = Boolean::allocated_constant(cs, false);

        // Prepating a point on the curve (just take 8*G where G is the generator)
        let mut point = BN256SWProjectivePoint::one(cs, &Arc::new(params));
        point = point.double(cs);
        point = point.double(cs);
        point = point.double(cs);
        let (point, at_infty) = point.convert_to_affine_or_default(cs, G1Affine::one());

        // Asserting we are not at infinity
        Boolean::enforce_equal(cs, &at_infty, &boolean_false);

        // Check if the point is on the curve
        let is_valid = validation::is_on_curve(cs, (&point.0, &point.1), &Arc::new(params));
        Boolean::enforce_equal(cs, &is_valid, &boolean_true);
    }

    /// Tests whether when inserted a valid point on the twisted curve, the 
    /// validation function returns true.
    #[test]
    fn test_on_twisted_curve_validation_valid() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 20);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();

        // Preparing booleans
        let boolean_true = Boolean::allocated_constant(cs, true);
        let boolean_false = Boolean::allocated_constant(cs, false);

        // Prepating a point on the curve (just take 16*G where G is the generator)
        let mut point = BN256SWProjectivePointTwisted::one(cs, &Arc::new(params));
        point = point.double(cs);
        point = point.double(cs);
        point = point.double(cs);
        point = point.double(cs);
        let (point, at_infty) = point.convert_to_affine_or_default(cs, G2Affine::one());

        // Asserting we are not at infinity
        Boolean::enforce_equal(cs, &at_infty, &boolean_false);

        // Check if the point is on the curve
        let is_valid = validation::is_on_twist_curve(cs, (&point.0, &point.1), &Arc::new(params));
        Boolean::enforce_equal(cs, &is_valid, &boolean_true);
    }

    /// Tests whether when inserted an invalid point on the regular curve, 
    /// the validation function returns false.
    #[test]
    fn test_on_curve_validation_invalid() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 20);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();
        let boolean_false = Boolean::allocated_constant(cs, false);

        // Prepating a point on the curve (just take 8*G where G is the generator)
        let mut point = BN256SWProjectivePoint::one(cs, &Arc::new(params));
        point = point.double(cs);
        point = point.double(cs);
        point = point.double(cs);
        let (mut point, at_infty) = point.convert_to_affine_or_default(cs, G1Affine::one());

        // Now, to make a point invalid, we simply add 1 to the x-coordinate
        let mut one = BN256BaseNNField::allocated_constant(cs, Fq::one(), &Arc::new(params));
        point.0 = point.0.add(cs, &mut one);

        // Asserting we are not at infinity
        Boolean::enforce_equal(cs, &at_infty, &boolean_false);

        // Check if the point is on the curve
        let is_valid = validation::is_on_curve(cs, (&point.0, &point.1), &Arc::new(params));
        Boolean::enforce_equal(cs, &is_valid, &boolean_false);
    }

    /// Tests whether when inserted an invalid point on the regular curve, 
    /// the validation function returns false.
    #[test]
    fn test_on_twisted_curve_validation_invalid() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 20);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();
        let boolean_false = Boolean::allocated_constant(cs, false);

        // Prepating a point on the curve (just take 8*G where G is the generator)
        let mut point = BN256SWProjectivePointTwisted::one(cs, &Arc::new(params));
        point = point.double(cs);
        point = point.double(cs);
        point = point.double(cs);
        let (mut point, at_infty) = point.convert_to_affine_or_default(cs, G2Affine::one());

        // Now, to make a point invalid, we simply add 1 to the x-coordinate
        let mut one = BN256Fq2NNField::allocated_constant(cs, Fq::one(), &Arc::new(params));
        point.0 = point.0.add(cs, &mut one);

        // Asserting we are not at infinity
        Boolean::enforce_equal(cs, &at_infty, &boolean_false);

        // Check if the point is on the curve
        let is_valid = validation::is_on_twist_curve(cs, (&point.0, &point.1), &Arc::new(params));
        Boolean::enforce_equal(cs, &is_valid, &boolean_false);
    }
}
