pub mod test {

    use std::sync::Arc;

    use crate::bn254::ec_pairing::final_exp::{
        CompressionMethod, FinalExpEvaluation, HardExpMethod,
    };
    use crate::bn254::ec_pairing::implementation::{
        ec_pairing, ec_pairing_inner, LineFunctionEvaluation, MillerLoopEvaluation,
    };
    use crate::bn254::tests::json::{
        FINAL_EXP_TEST_CASES, G2_CURVE_TEST_CASES, INVALID_SUBGROUP_TEST_CASES,
        LINE_FUNCTION_TEST_CASES, PAIRING_TEST_CASES,
    };
    use crate::bn254::tests::utils::assert::{
        assert_equal_fq12, assert_equal_fq2, assert_equal_g2_jacobian_points,
        assert_equal_g2_points, assert_not_equal_fq12,
    };
    use crate::bn254::tests::utils::cs::create_test_cs;
    use crate::bn254::tests::utils::debug_success;
    use crate::bn254::{
        bn254_base_field_params, BN256SWProjectivePoint, BN256SWProjectivePointTwisted,
    };
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::non_native_field::traits::NonNativeField;
    use boojum::pairing::bn256::{G1Affine, G2Affine};
    use boojum::pairing::CurveAffine;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Tests whether G2 curve operations are correct. Namely, we verify:
    ///
    /// 1. The sum of two points.
    /// 2. The double of a point.
    ///
    /// The test cases are loaded from the [`G2_CURVE_TEST_CASES`] constant.
    #[test]
    fn test_g2_curve() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in G2_CURVE_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut point_1 = test.point_1.to_projective_point(cs);
            let mut point_2 = test.point_2.to_projective_point(cs);

            let point_2_x = point_2.x.clone();
            let point_2_y = point_2.y.clone();

            // Expected:
            let mut expected_sum = test.expected.sum.to_projective_point(cs);
            let mut expected_point_1_double = test.expected.point_1_double.to_projective_point(cs);
            let mut expected_point_2_double = test.expected.point_2_double.to_projective_point(cs);

            // Actual:
            let mut sum = point_1.add_mixed(cs, &mut (point_2_x, point_2_y));
            let mut point_1_double = point_1.double(cs);
            let mut point_2_double = point_2.double(cs);

            // Asserting:
            assert_equal_g2_points(cs, &mut sum, &mut expected_sum);
            assert_equal_g2_points(cs, &mut point_1_double, &mut expected_point_1_double);
            assert_equal_g2_points(cs, &mut point_2_double, &mut expected_point_2_double);

            debug_success("G2", i, DEBUG_FREQUENCY);
        }
    }

    /// Tests the line function doubling step evaluation used in the pairing computation.
    ///
    /// The test cases are loaded from the [`LINE_FUNCTION_TEST_CASES`] constant.
    #[test]
    fn test_doubling_step() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        for (i, test) in LINE_FUNCTION_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut g2_point_1 = test.g2_point_1.to_projective_point(cs);
            let mut g2_point_2 = test.g2_point_2.to_projective_point(cs);
            let mut g1_point = test.g1_point.to_projective_point(cs);

            // Expected:3
            let mut expected_point_1 = test.expected.doubling_1.point.to_projective_point(cs);
            let mut expected_c0_1 = test.expected.doubling_1.c0.to_fq2(cs);
            let mut expected_c3_1 = test.expected.doubling_1.c3.to_fq2(cs);
            let mut expected_c4_1 = test.expected.doubling_1.c4.to_fq2(cs);

            let mut expected_point_2 = test.expected.doubling_2.point.to_projective_point(cs);
            let mut expected_c0_2 = test.expected.doubling_2.c0.to_fq2(cs);
            let mut expected_c3_2 = test.expected.doubling_2.c3.to_fq2(cs);
            let mut expected_c4_2 = test.expected.doubling_2.c4.to_fq2(cs);

            // Actual:
            let doubling_1 =
                LineFunctionEvaluation::doubling_step(cs, &mut g2_point_1, &mut g1_point);
            let mut point_1 = doubling_1.point();
            let (mut c0_1, mut c3_1, mut c4_1) = doubling_1.c0c3c4();

            let doubling_2 =
                LineFunctionEvaluation::doubling_step(cs, &mut g2_point_2, &mut g1_point);
            let mut point_2 = doubling_2.point();
            let (mut c0_2, mut c3_2, mut c4_2) = doubling_2.c0c3c4();

            // Asserting:
            assert_equal_g2_jacobian_points(cs, &mut point_1, &mut expected_point_1);
            assert_equal_fq2(cs, &mut c0_1, &mut expected_c0_1);
            assert_equal_fq2(cs, &mut c3_1, &mut expected_c3_1);
            assert_equal_fq2(cs, &mut c4_1, &mut expected_c4_1);

            assert_equal_g2_jacobian_points(cs, &mut point_2, &mut expected_point_2);
            assert_equal_fq2(cs, &mut c0_2, &mut expected_c0_2);
            assert_equal_fq2(cs, &mut c3_2, &mut expected_c3_2);
            assert_equal_fq2(cs, &mut c4_2, &mut expected_c4_2);

            println!("Line function test {} has passed!", i);
        }
    }

    /// Tests the line function addition step evaluation used in the pairing computation.
    ///
    /// The test cases are loaded from the [`LINE_FUNCTION_TEST_CASES`] constant.
    #[test]
    fn test_addition_step() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        for (i, test) in LINE_FUNCTION_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut g2_point_1 = test.g2_point_1.to_projective_point(cs);
            let mut g2_point_2 = test.g2_point_2.to_projective_point(cs);
            let mut g1_point = test.g1_point.to_projective_point(cs);

            // Expected:
            let mut expected_addition_point = test.expected.addition.point.to_projective_point(cs);
            let mut expected_c0 = test.expected.addition.c0.to_fq2(cs);
            let mut expected_c3 = test.expected.addition.c3.to_fq2(cs);
            let mut expected_c4 = test.expected.addition.c4.to_fq2(cs);

            // Actual:
            let addition = LineFunctionEvaluation::addition_step(
                cs,
                &mut g2_point_1,
                &mut g2_point_2,
                &mut g1_point,
            );
            let mut addition_point = addition.point();
            let (mut c0, mut c3, mut c4) = addition.c0c3c4();

            // Asserting:
            assert_equal_g2_jacobian_points(cs, &mut addition_point, &mut expected_addition_point);
            assert_equal_fq2(cs, &mut c0, &mut expected_c0);
            assert_equal_fq2(cs, &mut c3, &mut expected_c3);
            assert_equal_fq2(cs, &mut c4, &mut expected_c4);

            println!("Addition step function test {} has passed!", i);
        }
    }

    /// Tests the correctness of the following line operation inside the Miller Loop:
    /// - Double the first point
    /// - Add the second point
    ///
    /// The test cases are loaded from the [`LINE_FUNCTION_TEST_CASES`] constant.
    #[test]
    fn test_double_and_addition_step() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        for (i, test) in LINE_FUNCTION_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut g2_point_1 = test.g2_point_1.to_projective_point(cs);
            let mut g2_point_2 = test.g2_point_2.to_projective_point(cs);
            let mut g1_point = test.g1_point.to_projective_point(cs);

            // Expected:
            let mut expected_point = test
                .expected
                .doubling_1_and_addition
                .point
                .to_projective_point(cs);
            let mut expected_c0 = test.expected.doubling_1_and_addition.c0.to_fq2(cs);
            let mut expected_c3 = test.expected.doubling_1_and_addition.c3.to_fq2(cs);
            let mut expected_c4 = test.expected.doubling_1_and_addition.c4.to_fq2(cs);

            // Actual:
            let doubling =
                LineFunctionEvaluation::doubling_step(cs, &mut g2_point_1, &mut g1_point);
            g2_point_1 = doubling.point();
            let addition = LineFunctionEvaluation::addition_step(
                cs,
                &mut g2_point_2,
                &mut g2_point_1,
                &mut g1_point,
            );
            let mut actual_point = addition.point();
            let (mut c0, mut c3, mut c4) = addition.c0c3c4();

            // Asserting:
            assert_equal_g2_jacobian_points(cs, &mut actual_point, &mut expected_point);
            assert_equal_fq2(cs, &mut c0, &mut expected_c0);
            assert_equal_fq2(cs, &mut c3, &mut expected_c3);
            assert_equal_fq2(cs, &mut c4, &mut expected_c4);

            println!("Double&Addition step function test {} has passed!", i);
        }
    }

    /// Tests the Miller Loop step used in the pairing computation.
    ///
    /// The test cases are loaded from the [`PAIRING_TEST_CASES`] constant.
    #[test]
    fn test_miller_loop() {
        const DEBUG_PERFORMANCE: bool = true;

        // Running tests from file
        for (i, test) in PAIRING_TEST_CASES.tests.iter().enumerate() {
            // Preparing the constraint system and parameters
            let mut owned_cs = create_test_cs(1 << 18);
            let cs = &mut owned_cs;

            // Input:
            let mut g1_point = test.g1_point.to_projective_point(cs);
            let mut g2_point = test.g2_point.to_projective_point(cs);

            // Expected:
            let mut expected_miller_loop = test.miller_loop.to_fq12(cs);

            // Actual:
            let miller_loop = MillerLoopEvaluation::evaluate(cs, &mut g1_point, &mut g2_point);
            let mut miller_loop = miller_loop.get_accumulated_f();

            // Asserting:
            assert_equal_fq12(cs, &mut miller_loop, &mut expected_miller_loop);

            // Printing the number of constraints if needed
            if DEBUG_PERFORMANCE {
                let cs = owned_cs.into_assembly::<std::alloc::Global>();
                cs.print_gate_stats();
            }

            println!("Miller loop test {} has passed!", i);
        }
    }

    /// Tests the final exponentiation step used in the pairing computation.
    ///
    /// At the beginning of the test, one can specify the hard exponentiation method to use
    /// and whether to debug the number of rows in the constraint system.
    ///
    /// The test cases are loaded from the [`FINAL_EXP_TEST_CASES`] constant.
    #[test]
    fn test_final_exponentiation() {
        const HARD_EXP_METHOD: HardExpMethod = HardExpMethod::Naive;
        const COMPRESSION_METHOD: CompressionMethod = CompressionMethod::None;
        const DEBUG_PERFORMANCE: bool = true;

        // Running tests from file
        for (i, test) in FINAL_EXP_TEST_CASES.tests.iter().enumerate() {
            // Preparing the constraint system and parameters
            let mut owned_cs = create_test_cs(1 << 19);
            let cs = &mut owned_cs;

            // Expected:
            let expected_f_final = test.expected.to_fq12(cs);

            // Actual:
            let mut f = test.scalar.to_fq12(cs);
            let f_final =
                FinalExpEvaluation::evaluate(cs, &mut f, HARD_EXP_METHOD, COMPRESSION_METHOD);
            let f_final = f_final.get();

            // Asserting:
            assert_equal_fq12(cs, &f_final, &expected_f_final);

            // Printing the number of constraints if needed
            if DEBUG_PERFORMANCE {
                let cs = owned_cs.into_assembly::<std::alloc::Global>();
                cs.print_gate_stats();
            }

            println!("Final exponentiation test {} has passed!", i);
        }
    }

    /// Tests the EC pairing as a whole by comparing output with the one retrieved from the Sage implementation.
    ///
    /// At the beginning of the test, one can specify the hard exponentiation method to use
    /// and whether to debug the number of rows in the constraint system.
    ///
    /// The test cases are loaded from the [`PAIRING_TEST_CASES`] constant.
    #[test]
    fn test_ec_pairing_inner() {
        const HARD_EXP_METHOD: HardExpMethod = HardExpMethod::Naive;
        const COMPRESSION_METHOD: CompressionMethod = CompressionMethod::AlgebraicTorus;
        const DEBUG_PERFORMANCE: bool = true;

        // Running tests from file
        for (i, test) in PAIRING_TEST_CASES.tests.iter().enumerate() {
            // Preparing the constraint system and parameters
            let mut owned_cs = create_test_cs(1 << 20);
            let cs = &mut owned_cs;

            // Input:
            let mut g1_point = test.g1_point.to_projective_point(cs);
            let mut g2_point = test.g2_point.to_projective_point(cs);

            // Expected:
            let mut expected_pairing = test.pairing.to_fq12(cs);

            // Actual:
            let mut pairing = ec_pairing_inner(
                cs,
                &mut g1_point,
                &mut g2_point,
                HARD_EXP_METHOD,
                COMPRESSION_METHOD,
            );

            // Asserting:
            assert_equal_fq12(cs, &mut pairing, &mut expected_pairing);

            if DEBUG_PERFORMANCE {
                let cs = owned_cs.into_assembly::<std::alloc::Global>();
                cs.print_gate_stats();
            }
            println!("EC pairing test {} has passed!", i);
        }
    }

    /// Tests the bilinearity of the EC pairing. Namely, we test that
    ///
    /// `e([a]P,[b]Q) = e([b]P, [a]Q)`
    ///
    /// Here, we use `a=2,b=1` and `P=Q=one`.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn test_ec_pairing_bilinearity() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 22);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();

        // Input (two points g1 and g2):
        let mut g1_point = BN256SWProjectivePoint::one(cs, &Arc::new(params));
        let mut g2_point = BN256SWProjectivePointTwisted::one(cs, &Arc::new(params));

        // Calculating e(2*g1,g2) and e(g1,2*g2). Asserting they are equal.
        let mut g1_point_double = g1_point.double(cs);
        let mut g2_point_double = g2_point.double(cs);

        // Since z components of 2*g1 and 2*g2 are not equal to 1, we need to convert them to affine
        let ((x, y), _) = g1_point_double.convert_to_affine_or_default(cs, G1Affine::zero());
        let mut g1_point_double = BN256SWProjectivePoint::from_xy_unchecked(cs, x, y);
        g1_point_double.x.normalize(cs);
        g1_point_double.y.normalize(cs);

        let ((x, y), _) = g2_point_double.convert_to_affine_or_default(cs, G2Affine::zero());
        let mut g2_point_double = BN256SWProjectivePointTwisted::from_xy_unchecked(cs, x, y);
        g2_point_double.x.normalize(cs);
        g2_point_double.y.normalize(cs);

        g1_point_double.enforce_reduced(cs);
        g2_point_double.enforce_reduced(cs);

        let mut pairing_1 = ec_pairing(cs, &mut g1_point_double, &mut g2_point);
        let mut pairing_2 = ec_pairing(cs, &mut g1_point, &mut g2_point_double);

        // Asserting:
        assert_equal_fq12(cs, &mut pairing_1, &mut pairing_2);

        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
        println!("EC pairing bilinearity test has passed!");
    }

    /// Tests the unsatisfiability of the EC pairing when the points are not in the correct subgroup,
    /// so in other words when, for example, `P` and `Q` are not in the r-torsion subgroup.
    ///
    /// The test takes invalid `Q` G2 point from the [`INVALID_SUBGROUP_TEST_CASES`] constant and tries to compute the pairing
    /// of `e([2]P,Q)` and `e(P,[2]Q)`. The values should not be equal.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn test_ec_pairing_non_subgroup_unsatisfiability() {
        const HARD_EXP_METHOD: HardExpMethod = HardExpMethod::Naive;
        const COMPRESSION_METHOD: CompressionMethod = CompressionMethod::None;
        const DEBUG_PERFORMANCE: bool = true;

        // Running tests from file
        for (i, test) in INVALID_SUBGROUP_TEST_CASES.tests.iter().enumerate() {
            // Preparing the constraint system and parameters
            let mut owned_cs = create_test_cs(1 << 22);
            let cs = &mut owned_cs;

            // Input:
            let mut g1_point = test.g1_point.to_projective_point(cs);
            let mut g2_point = test.g2_point.to_projective_point(cs);
            let mut g1_point_doubled = test.g1_point_doubled.to_projective_point(cs);
            let mut g2_point_doubled = test.g2_point_doubled.to_projective_point(cs);

            // Calculating two pairings:
            let mut pairing_ab = ec_pairing_inner(
                cs,
                &mut g1_point_doubled,
                &mut g2_point,
                HARD_EXP_METHOD,
                COMPRESSION_METHOD,
            );
            let mut pairing_ba = ec_pairing_inner(
                cs,
                &mut g1_point,
                &mut g2_point_doubled,
                HARD_EXP_METHOD,
                COMPRESSION_METHOD,
            );

            // Asserting:
            assert_not_equal_fq12(cs, &mut pairing_ab, &mut pairing_ba);

            if DEBUG_PERFORMANCE {
                let cs = owned_cs.into_assembly::<std::alloc::Global>();
                cs.print_gate_stats();
            }
            println!("EC pairing invalid subgroup test {} has passed!", i);
        }
    }

    /// Tests the validation in EC pairing. That is, when we place two non-normalized points in the pairing function,
    /// the function should panic.
    /// 
    /// This test checks what happens if the first point (on the regular curve) is not normalized.
    #[test]
    #[should_panic]
    fn test_ec_pairing_invalid_point_1() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 22);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();

        // Calculating two generators and double the first one
        let mut g1_point = BN256SWProjectivePoint::one(cs, &Arc::new(params));
        let mut g2_point = BN256SWProjectivePointTwisted::one(cs, &Arc::new(params));
        let mut g1_point_double = g1_point.double(cs);

        // NOTE: Here, z coordinates are not equal to 1, and thus without normalization,
        // the EC pairing function should panic
        let _ = ec_pairing(cs, &mut g1_point_double, &mut g2_point);
    }

    /// Tests the validation in EC pairing. That is, when we place two non-normalized points in the pairing function,
    /// the function should panic.
    /// 
    /// This test checks what happens if the second point (on the twisted curve) is not normalized.
    #[test]
    #[should_panic]
    fn test_ec_pairing_invalid_point_2() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 22);
        let cs = &mut owned_cs;
        let params = bn254_base_field_params();

        // Calculating two generators and double the second one
        let mut g1_point = BN256SWProjectivePoint::one(cs, &Arc::new(params));
        let mut g2_point = BN256SWProjectivePointTwisted::one(cs, &Arc::new(params));
        let mut g2_point_double = g2_point.double(cs);

        // NOTE: Here, z coordinates are not equal to 1, and thus without normalization,
        // the EC pairing function should panic
        let _ = ec_pairing(cs, &mut g1_point, &mut g2_point_double);
    }
}
