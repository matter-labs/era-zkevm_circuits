pub mod test {
    use crate::bn254::ec_pairing::final_exp::U_WNAF;
    use crate::bn254::tests::json::TORUS_TEST_CASES;
    use crate::bn254::tests::utils::assert::assert_equal_fq6;
    use crate::bn254::tests::utils::cs::create_test_cs;
    use crate::bn254::tests::utils::debug_success;
    use crate::bn254::BN256TorusWrapper;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::tower_extension::algebraic_torus::TorusWrapper;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Test the compression and decompression functions in Algebraic Torus.
    ///
    /// The tests are run against the test cases defined in [`TORUS_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/torus.sage`.
    #[test]
    fn test_torus_compression() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating correctness of encoded values
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in TORUS_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);
            let mut scalar_2 = test.scalar_2.to_fq12(cs);

            // Actual (compressing inputs):
            let scalar_1_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_1);
            let scalar_2_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_2);

            // Expected:
            let expected_encoding_1 = test.expected.encoding_1.to_fq6(cs);
            let expected_encoding_2 = test.expected.encoding_2.to_fq6(cs);

            // Asserting:
            assert_equal_fq6(cs, &scalar_1_torus.encoding, &expected_encoding_1);
            assert_equal_fq6(cs, &scalar_2_torus.encoding, &expected_encoding_2);

            debug_success("torus compression", i, DEBUG_FREQUENCY);
        }
    }

    /// Test basic arithmetic on Algebraic Torus.
    ///
    /// - multiplication (`.mul`)
    /// - inverse (`.inverse`)
    /// - conjugate (`.conjugate`)
    /// - squaring (`.square`)
    ///
    /// The tests are run against the test cases defined in [`TORUS_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/torus.sage`.
    #[test]
    fn test_torus_basic_arithmetic() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in TORUS_TEST_CASES.tests.iter().enumerate() {
            // Reading inputs
            let mut scalar_1 = test.scalar_1.to_fq12(cs);
            let mut scalar_2 = test.scalar_2.to_fq12(cs);

            // Compressing inputs
            let mut scalar_1_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_1);
            let mut scalar_2_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_2);
            // Expected:
            let expected_product = test.expected.product_encoding.to_fq6(cs);
            let expected_inverse_1 = test.expected.inverse_1_encoding.to_fq6(cs);
            let expected_conjugate_1 = test.expected.conjugate_1_encoding.to_fq6(cs);
            let expected_square_1 = test.expected.square_1_encoding.to_fq6(cs);

            // Actual:
            let product = scalar_1_torus.mul(cs, &mut scalar_2_torus);
            let inverse_1 = scalar_1_torus.inverse(cs);
            let conjugate_1 = scalar_1_torus.conjugate(cs);
            let square_1 = scalar_1_torus.square(cs);

            // Asserting:
            assert_equal_fq6(cs, &product.encoding, &expected_product);
            assert_equal_fq6(cs, &inverse_1.encoding, &expected_inverse_1);
            assert_equal_fq6(cs, &conjugate_1.encoding, &expected_conjugate_1);
            assert_equal_fq6(cs, &square_1.encoding, &expected_square_1);

            debug_success("torus basic arithmetic", i, DEBUG_FREQUENCY);
        }
    }

    /// Tests the frobenius map `x^p^k` on Algebraic Torus for `k=1,2,3`.
    ///
    /// The tests are run against the test cases defined in [`TORUS_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/torus.sage`.
    #[test]
    fn test_torus_frobenius_map() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in TORUS_TEST_CASES.tests.iter().enumerate() {
            // Reading input (only the first scalar)
            let mut scalar_1 = test.scalar_1.to_fq12(cs);

            // Compressing input (only the first scalar)
            let mut scalar_1_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

            // Expected:
            let expected_frobenius_1 = test.expected.frobenius_1_encoding.to_fq6(cs);
            let expected_frobenius_2 = test.expected.frobenius_2_encoding.to_fq6(cs);
            let expected_frobenius_3 = test.expected.frobenius_3_encoding.to_fq6(cs);

            // Actual:
            let frobenius_1 = scalar_1_torus.frobenius_map(cs, 1);
            let frobenius_2 = scalar_1_torus.frobenius_map(cs, 2);
            let frobenius_3 = scalar_1_torus.frobenius_map(cs, 3);

            // Asserting:
            assert_equal_fq6(cs, &frobenius_1.encoding, &expected_frobenius_1);
            assert_equal_fq6(cs, &frobenius_2.encoding, &expected_frobenius_2);
            assert_equal_fq6(cs, &frobenius_3.encoding, &expected_frobenius_3);

            debug_success("torus frobenius map", i, DEBUG_FREQUENCY);
        }
    }

    /// Tests the u32 power operation over Algebraic Torus.
    ///
    /// The tests are run against the test cases defined in [`TORUS_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/torus.sage`.
    #[test]
    fn test_torus_power_u32() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in TORUS_TEST_CASES.tests.iter().enumerate() {
            // Reading input (only the first scalar)
            let mut scalar_1 = test.scalar_1.to_fq12(cs);

            // Compressing input (only the first scalar)
            let mut scalar_1_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

            // Expected:
            let expected_power_u = test.expected.power_u_encoding.to_fq6(cs);
            let expected_power_13 = test.expected.power_13_encoding.to_fq6(cs);

            let power_u = scalar_1_torus.pow_u32(cs, &[4965661367192848881]);
            let power_13 = scalar_1_torus.pow_u32(cs, &[13]);

            // Asserting:
            assert_equal_fq6(cs, &power_u.encoding, &expected_power_u);
            assert_equal_fq6(cs, &power_13.encoding, &expected_power_13);

            debug_success("torus raising to power", i, DEBUG_FREQUENCY);
        }
    }

    /// Tests the power operation using naf decomposition over Algebraic Torus.
    ///
    /// The tests are run against the test cases defined in [`TORUS_TEST_CASES`], which
    /// are generated using the `sage` script in `gen/torus.sage`.
    #[test]
    fn test_torus_naf_power() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file: validating sum, diff, prod, and quot
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in TORUS_TEST_CASES.tests.iter().enumerate() {
            // Reading input (only the first scalar)
            let u = U_WNAF;
            let mut scalar_1 = test.scalar_1.to_fq12(cs);

            // Compressing input (only the first scalar)
            let mut scalar_1_torus: BN256TorusWrapper<F> =
                TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

            // Expected:
            let expected_power_u = test.expected.power_u_encoding.to_fq6(cs);
            let expected_power_13 = test.expected.power_13_encoding.to_fq6(cs);

            // Actual:
            let power_u = scalar_1_torus.pow_naf_decomposition(cs, u);
            let power_13 =
                scalar_1_torus.pow_naf_decomposition(cs, &[1, 0, -1, 0, 1]);

            // Asserting:
            assert_equal_fq6(cs, &power_u.encoding, &expected_power_u);
            assert_equal_fq6(cs, &power_13.encoding, &expected_power_13);

            debug_success("torus raising to power", i, DEBUG_FREQUENCY);
        }
    }
}
