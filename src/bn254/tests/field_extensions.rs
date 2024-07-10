pub mod test {

    use crate::bn254::tests::json::{FQ12_TEST_CASES, FQ2_TEST_CASES, FQ6_TEST_CASES};
    use crate::bn254::tests::utils::assert::{
        assert_equal_fq12, assert_equal_fq2, assert_equal_fq6
    };
    use crate::bn254::tests::utils::cs::create_test_cs;
    use crate::bn254::tests::utils::debug_success;
    use boojum::field::goldilocks::GoldilocksField;
    
    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Test basic arithmetic of `Fq2` field extension, namely:
    ///
    /// - sum (`.add`)
    /// - difference (`.sub`)
    /// - product (`.mul`)
    /// - quotient (`.div`)
    ///
    /// The tests are run against the test cases defined in [`FQ2_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq2_basic_arithmetic() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ2_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq2(cs);
            let mut scalar_2 = test.scalar_2.to_fq2(cs);

            // Expected:
            let expected_sum = test.expected.sum.to_fq2(cs);
            let expected_difference = test.expected.difference.to_fq2(cs);
            let expected_product = test.expected.product.to_fq2(cs);
            let expected_quotient = test.expected.quotient.to_fq2(cs);

            // Actual:
            let sum = scalar_1.add(cs, &mut scalar_2);
            let difference = scalar_1.sub(cs, &mut scalar_2);
            let product = scalar_1.mul(cs, &mut scalar_2);
            let quotient = scalar_1.div(cs, &mut scalar_2);

            // Asserting:
            assert_equal_fq2(cs, &sum, &expected_sum);
            assert_equal_fq2(cs, &difference, &expected_difference);
            assert_equal_fq2(cs, &product, &expected_product);
            assert_equal_fq2(cs, &quotient, &expected_quotient);

            debug_success("Fq2 basic arithmetic", i, DEBUG_FREQUENCY);
        }
    }

    /// Test multiplication by a non-residue of `Fq2` field extension.
    ///
    /// The tests are run against the test cases defined in [`FQ2_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq2_non_residue() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ2_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq2(cs);

            // Expected:
            let expected_scalar_1_nonresidue = test.expected.scalar_1_non_residue.to_fq2(cs);

            // Actual:
            let scalar_1_non_residue = scalar_1.mul_by_nonresidue(cs);

            // Asserting:
            assert_equal_fq2(cs, &scalar_1_non_residue, &expected_scalar_1_nonresidue);

            debug_success("Fq2 non-residue", i, DEBUG_FREQUENCY);
        }
    }

    /// Test frobenius map of `Fq2` field extension.
    ///
    /// The tests are run against the test cases defined in [`FQ2_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq2_frobenius() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ2_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq2(cs);

            // Expected:
            let expected_frobenius_6 = test.expected.frobenius_6.to_fq2(cs);

            // Actual:
            let frobenius_6 = scalar_1.frobenius_map(cs, 6);

            // Asserting:
            assert_equal_fq2(cs, &frobenius_6, &expected_frobenius_6);

            debug_success("Fq2 frobenius", i, DEBUG_FREQUENCY);
        }
    }

    /// Test basic arithmetic of `Fq6` field extension, namely:
    ///
    /// - sum (`.add`)
    /// - difference (`.sub`)
    /// - product (`.mul`)
    /// - quotient (`.div`)
    /// - squaring (`.square`)
    /// - inverse (`.inverse`)
    /// - multiplication by a non-residue (`.mul_by_nonresidue`)
    ///
    /// The tests are run against the test cases defined in [`FQ6_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq6_basic_arithmetic() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ6_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq6(cs);
            let mut scalar_2 = test.scalar_2.to_fq6(cs);

            // Expected:
            let expected_sum = test.expected.sum.to_fq6(cs);
            let expected_difference = test.expected.difference.to_fq6(cs);
            let expected_product = test.expected.product.to_fq6(cs);
            let expected_quotient = test.expected.quotient.to_fq6(cs);
            let expected_scalar_1_inverse = test.expected.scalar_1_inverse.to_fq6(cs);
            let expected_scalar_1_square = test.expected.scalar_1_square.to_fq6(cs);
            let expected_scalar_1_non_residue = test.expected.scalar_1_non_residue.to_fq6(cs);

            // Actual:
            let sum = scalar_1.add(cs, &mut scalar_2);
            let difference = scalar_1.sub(cs, &mut scalar_2);
            let product = scalar_1.mul(cs, &mut scalar_2);
            let quotient = scalar_1.div(cs, &mut scalar_2);
            let scalar_1_inverse = scalar_1.inverse(cs);
            let scalar_1_square = scalar_1.square(cs);
            let scalar_1_non_residue = scalar_1.mul_by_nonresidue(cs);

            // Asserting:
            assert_equal_fq6(cs, &sum, &expected_sum);
            assert_equal_fq6(cs, &difference, &expected_difference);
            assert_equal_fq6(cs, &product, &expected_product);
            assert_equal_fq6(cs, &quotient, &expected_quotient);
            assert_equal_fq6(cs, &scalar_1_inverse, &expected_scalar_1_inverse);
            assert_equal_fq6(cs, &scalar_1_square, &expected_scalar_1_square);
            assert_equal_fq6(cs, &scalar_1_non_residue, &expected_scalar_1_non_residue);

            debug_success("Fq6 basic arithmetic", i, DEBUG_FREQUENCY);
        }
    }

    /// Test multiplication by a non-residue of `Fq6` field extension, namely
    ///
    /// - multiplication by `c1` (`.mul_by_c1`)
    /// - multiplication by `c0+c1*v` (`.mul_by_c0c1`)
    /// - multiplication by `c2*v^2` (`.mul_by_c2`)
    ///
    /// The tests are run against the test cases defined in [`FQ6_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq6_sparse_mul() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ6_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq6(cs);
            let mut c0 = test.c0.to_fq2(cs);
            let mut c1 = test.c1.to_fq2(cs);
            let mut c2 = test.c2.to_fq2(cs);

            // Expected:
            let expected_product_c1 = test.expected.product_c1.to_fq6(cs);
            let expected_product_c0c1 = test.expected.product_c0c1.to_fq6(cs);
            let expected_product_c2 = test.expected.product_c2.to_fq6(cs);

            // Actual:
            let product_c1 = scalar_1.mul_by_c1(cs, &mut c1);
            let product_c0c1 = scalar_1.mul_by_c0c1(cs, &mut c0, &mut c1);
            let product_c2 = scalar_1.mul_by_c2(cs, &mut c2);

            // Asserting:
            assert_equal_fq6(cs, &product_c1, &expected_product_c1);
            assert_equal_fq6(cs, &product_c0c1, &expected_product_c0c1);
            assert_equal_fq6(cs, &product_c2, &expected_product_c2);

            debug_success("Fq6 sparse operations", i, DEBUG_FREQUENCY);
        }
    }

    /// Test frobenius map of `Fq6` field extension.
    ///
    /// The tests are run against the test cases defined in [`FQ6_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq6_frobenius() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in FQ6_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let mut scalar_1 = test.scalar_1.to_fq6(cs);
            let mut scalar_2 = test.scalar_2.to_fq6(cs);

            // Expected:
            let expected_frobenius_1 = test.expected.scalar_1_frobenius_1.to_fq6(cs);
            let expected_frobenius_2 = test.expected.scalar_2_frobenius_2.to_fq6(cs);
            let expected_frobenius_3 = test.expected.scalar_1_frobenius_3.to_fq6(cs);

            // Actual:
            let frobenius_1 = scalar_1.frobenius_map(cs, 1);
            let frobenius_2 = scalar_2.frobenius_map(cs, 2);
            let frobenius_3 = scalar_1.frobenius_map(cs, 3);

            // Asserting:
            assert_equal_fq6(cs, &frobenius_1, &expected_frobenius_1);
            assert_equal_fq6(cs, &frobenius_2, &expected_frobenius_2);
            assert_equal_fq6(cs, &frobenius_3, &expected_frobenius_3);

            debug_success("Fq6 frobenius", i, DEBUG_FREQUENCY);
        }
    }

    /// Test basic arithmetic of `Fq12` field extension, namely:
    ///
    /// - sum (`.add`)
    /// - difference (`.sub`)
    /// - product (`.mul`)
    /// - quotient (`.div`)
    /// - squaring (`.square`)
    /// - inverse (`.inverse`)
    ///
    /// The tests are run against the test cases defined in [`FQ12_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq12_basic_arithmetic() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in FQ12_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);
            let mut scalar_2 = test.scalar_2.to_fq12(cs);

            // Expected:
            let expected_sum = test.expected.sum.to_fq12(cs);
            let expected_difference = test.expected.difference.to_fq12(cs);
            let expected_product = test.expected.product.to_fq12(cs);
            let expected_quotient = test.expected.quotient.to_fq12(cs);
            let expected_scalar_1_inverse = test.expected.scalar_1_inverse.to_fq12(cs);
            let expected_scalar_1_square = test.expected.scalar_1_square.to_fq12(cs);

            // Actual:
            let sum = scalar_1.add(cs, &mut scalar_2);
            let difference = scalar_1.sub(cs, &mut scalar_2);
            let product = scalar_1.mul(cs, &mut scalar_2);
            let quotient = scalar_1.div(cs, &mut scalar_2);
            let scalar_1_inverse = scalar_1.inverse(cs);
            let scalar_1_square = scalar_1.square(cs);

            // Asserting:
            assert_equal_fq12(cs, &sum, &expected_sum);
            assert_equal_fq12(cs, &difference, &expected_difference);
            assert_equal_fq12(cs, &product, &expected_product);
            assert_equal_fq12(cs, &quotient, &expected_quotient);
            assert_equal_fq12(cs, &scalar_1_inverse, &expected_scalar_1_inverse);
            assert_equal_fq12(cs, &scalar_1_square, &expected_scalar_1_square);

            debug_success("Fq12 basic arithmetic", i, DEBUG_FREQUENCY);
        }
    }

    /// Test frobenius map of `Fq12` field extension.
    ///
    /// The tests are run against the test cases defined in [`FQ12_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq12_frobenius() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in FQ12_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);
            let mut scalar_2 = test.scalar_2.to_fq12(cs);

            // Expected:
            let expected_frobenius_1 = test.expected.scalar_1_frobenius_1.to_fq12(cs);
            let expected_frobenius_2 = test.expected.scalar_2_frobenius_2.to_fq12(cs);
            let expected_frobenius_3 = test.expected.scalar_1_frobenius_3.to_fq12(cs);

            // Actual:
            let frobenius_1 = scalar_1.frobenius_map(cs, 1);
            let frobenius_2 = scalar_2.frobenius_map(cs, 2);
            let frobenius_3 = scalar_1.frobenius_map(cs, 3);

            // Asserting:
            assert_equal_fq12(cs, &frobenius_1, &expected_frobenius_1);
            assert_equal_fq12(cs, &frobenius_2, &expected_frobenius_2);
            assert_equal_fq12(cs, &frobenius_3, &expected_frobenius_3);

            debug_success("fp12 frobenius", i, DEBUG_FREQUENCY);
        }
    }

    /// Test sparse multiplication of `Fq12` field extension. Namely:
    ///
    /// - multiplication by `c0+(c3+c4*v)*w` (`.mul_by_c0c3c4`)
    /// - multiplication by `c0+c1*v+c4*v*w` (`.mul_by_c0c1c4`)
    ///
    /// The tests are run against the test cases defined in [`FQ12_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/field_extensions.sage`.
    #[test]
    fn test_fq12_sparse_mul() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in FQ12_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);
            let mut c0 = test.c0.to_fq2(cs);
            let mut c1 = test.c1.to_fq2(cs);
            let mut c3 = test.c3.to_fq2(cs);
            let mut c4 = test.c4.to_fq2(cs);
            let mut c5 = test.c5.to_fq2(cs);

            // Expected:
            let expected_product_c0c3c4 = test.expected.product_c0c3c4.to_fq12(cs);
            let expected_product_c0c1c4 = test.expected.product_c0c1c4.to_fq12(cs);
            let expected_product_c5 = test.expected.product_c5.to_fq12(cs);

            // Actual:
            let product_c0c3c4 = scalar_1.mul_by_c0c3c4(cs, &mut c0, &mut c3, &mut c4);
            let product_c0c1c4 = scalar_1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);
            let product_c5 = scalar_1.mul_by_c5(cs, &mut c5);

            // Asserting:
            assert_equal_fq12(cs, &product_c0c3c4, &expected_product_c0c3c4);
            assert_equal_fq12(cs, &product_c0c1c4, &expected_product_c0c1c4);
            assert_equal_fq12(cs, &product_c5, &expected_product_c5);

            debug_success("fq12 sparse mul", i, DEBUG_FREQUENCY);
        }
    }

    /// Test powering of `Fq12` field extension by a fixed u64 scalar.
    #[test]
    fn test_fq12_pow() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 23);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in FQ12_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);

            // Expected:
            let expected_pow_33 = test.expected.scalar_1_pow_33.to_fq12(cs);
            let expected_pow_u = test.expected.scalar_1_pow_u.to_fq12(cs);

            // Actual:
            const U: u64 = 4965661367192848881;
            let pow_33 = scalar_1.pow_u32(cs, &[33]);
            let pow_u = scalar_1.pow_u32(cs, &[U]);

            // Asserting:
            assert_equal_fq12(cs, &pow_33, &expected_pow_33);
            assert_equal_fq12(cs, &pow_u, &expected_pow_u);

            debug_success("fq12 power", i, DEBUG_FREQUENCY);
        }
    }
}
