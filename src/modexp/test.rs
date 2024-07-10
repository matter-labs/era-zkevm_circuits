pub mod test {
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::{new_builder, CsBuilder, CsBuilderImpl};
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::{
        BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
        FmaGateInBaseFieldWithoutConstant, NopGate, ReductionGate, SelectionGate, U8x4FMAGate,
        UIntXAddGate, ZeroCheckGate,
    };
    use boojum::cs::implementations::reference_cs::CSReferenceImplementation;
    use boojum::cs::traits::cs::ConstraintSystem;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::{CSGeometry, GateConfigurationHolder, LookupParameters, StaticToolboxHolder};
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::field::SmallField;
    use boojum::gadgets::boolean::Boolean;
    use boojum::gadgets::tables::{
        create_and8_table, create_byte_split_table, create_xor8_table, And8Table, ByteSplitTable,
        Xor8Table,
    };
    use boojum::gadgets::u2048::UInt2048;
    use boojum::gadgets::u256::UInt256;

    use crate::modexp::implementation::u256::{modexp_32_32_32, modexp_32_4_32};
    use crate::modexp::tests_json::u2048::Modmul256BytesTestCase;
    use crate::modexp::tests_json::u256::{
        Modexp32BytesLargeExpTestCase, Modexp32BytesSmallExpTestCase, Modmul32BytesTestCase,
    };
    use crate::modexp::tests_json::{
        MODEXP_32_32_32_TEST_CASES, MODEXP_32_4_32_TEST_CASES, MODMUL_256_256_TEST_CASES,
        MODMUL_32_32_TEST_CASES,
    };

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Creates a test constraint system for testing purposes
    pub fn create_test_cs(
        max_trace_len: usize,
    ) -> CSReferenceImplementation<
        F,
        P,
        DevCSConfig,
        impl GateConfigurationHolder<F>,
        impl StaticToolboxHolder,
    > {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 200,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 4,
        };
        let max_variables = 1 << 26;

        fn configure<
            F: SmallField,
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: 8,
                    share_table_id: true,
                },
            );
            let builder = U8x4FMAGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // let owned_cs = ReductionGate::<F, 4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 8, share_constants: true });
            let builder = BooleanConstraintGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<32>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<16>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = UIntXAddGate::<8>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = SelectionGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );
            let builder = DotProductGate::<4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // let owned_cs = DotProductGate::<4>::configure_for_cs(owned_cs, GatePlacementStrategy::UseSpecializedColumns { num_repetitions: 1, share_constants: true });
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(max_variables);

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_and8_table();
        owned_cs.add_lookup_table::<And8Table, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);
        let table = create_byte_split_table::<F, 2>();
        owned_cs.add_lookup_table::<ByteSplitTable<2>, 3>(table);
        let table = create_byte_split_table::<F, 3>();
        owned_cs.add_lookup_table::<ByteSplitTable<3>, 3>(table);
        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);
        let table = create_byte_split_table::<F, 7>();
        owned_cs.add_lookup_table::<ByteSplitTable<7>, 3>(table);

        owned_cs
    }

    fn assert_equal_uint256<CS>(cs: &mut CS, a: &UInt256<F>, b: &UInt256<F>)
    where
        CS: ConstraintSystem<F>,
    {
        let equals = UInt256::equals(cs, a, b);
        let boolean_true = Boolean::allocated_constant(cs, true);
        Boolean::enforce_equal(cs, &equals, &boolean_true);
    }

    fn assert_equal_uint2048<CS>(cs: &mut CS, a: &UInt2048<F>, b: &UInt2048<F>)
    where
        CS: ConstraintSystem<F>,
    {
        let equals = UInt2048::equals(cs, a, b);
        let boolean_true = Boolean::allocated_constant(cs, true);
        Boolean::enforce_equal(cs, &equals, &boolean_true);
    }

    /// This function tests the modular exponentiation, that is
    /// an operation `b^e mod m`, where b is the base, e is the exponent,
    /// and m is the modulus when (b,e,m) are 32-bytes long.
    ///
    /// The function reads the test cases from [`MODEXP_32_32_32_TEST_CASES`] and runs them.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn test_modexp_32_32_32() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 22);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODEXP_32_32_32_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = Modexp32BytesLargeExpTestCase::from_raw(cs, &raw);

            // Expected:
            let actual_modexp = modexp_32_32_32(cs, &test.base, &test.exponent, &test.modulus);

            // Actual:
            let expected_modexp = test.expected.clone();

            // Asserting
            assert_equal_uint256(cs, &actual_modexp, &expected_modexp);
        }
    }

    /// This function tests the modular exponentiation, that is
    /// an operation `b^e mod m`, where b is the base, e is the exponent,
    /// and m is the modulus when (b,m) are 32-bytes long, and e is a 4-byte integer.
    ///
    /// The function reads the test cases from [`MODEXP_32_4_32_TEST_CASES`] and runs them.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn test_modexp_32_4_32() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 24);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODEXP_32_4_32_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = Modexp32BytesSmallExpTestCase::from_raw(cs, &raw);

            // Expected:
            let actual_modexp = modexp_32_4_32(cs, &test.base, &test.exponent, &test.modulus);

            // Actual:
            let expected_modexp = test.expected.clone();

            // Asserting
            assert_equal_uint256(cs, &actual_modexp, &expected_modexp);
        }

        // Printing the number of constraints
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// This function tests the modular multiplication, that is
    /// an operation `a*b mod m`, where a and b are two integers,
    /// e is the exponent, and m is the modulus.
    ///
    /// The function reads the test cases from [`MODMUL_32_32_TEST_CASES`] and runs them.
    #[test]
    fn test_modmul_32_32() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 20);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODMUL_32_32_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = Modmul32BytesTestCase::from_raw(cs, &raw);

            // Actual:
            let actual_modmul = test.a.modmul(cs, &test.b, &test.modulus);

            // Expected:
            let expected_modmul = test.expected.clone();

            // Asserting
            assert_equal_uint256(cs, &actual_modmul, &expected_modmul);
        }
    }

    /// This function runs an operation `a*b mod m`, where a and b are two integers,
    /// e is the exponent, m is the modulus, and checks the number of constraints.
    #[test]
    #[ignore = "debugs the performance, should be run manually"]
    fn debug_modmul_32_32_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        let raw = &MODMUL_32_32_TEST_CASES.tests[0];
        // Input:
        let test_case = Modmul32BytesTestCase::from_raw(cs, &raw);

        // Actual:
        let _ = test_case.a.modmul(cs, &test_case.b, &test_case.modulus);

        // Printing the number of constraints
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// This function tests the modular multiplication, that is
    /// an operation `a*b mod m`, where a and b are two integers,
    /// e is the exponent, and m is the modulus.
    ///
    /// The function reads the test cases from [`MODMUL_256_256_TEST_CASES`] and runs them.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn test_modmul_256_bytes() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 24);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODMUL_256_256_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = Modmul256BytesTestCase::from_raw(cs, &raw);

            // Expected:
            let actual_modmul = test.a.modmul(cs, &test.b, &test.modulus);

            // Actual:
            let expected_modmul = test.expected.clone();

            // Asserting
            assert_equal_uint2048(cs, &actual_modmul, &expected_modmul);
        }

        // Printing the number of constraints
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// This function runs an operation `a*b mod m`, where a and b are two integers,
    /// e is the exponent, m is the modulus, and checks the number of constraints.
    ///
    /// The function reads the test cases from [`MODMUL_256_256_TEST_CASES`] and runs them.
    #[test]
    #[ignore = "too-large circuit, should be run manually"]
    fn debug_modmul_256_bytes() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 26);
        let cs = &mut owned_cs;

        // Input:
        let raw = &MODMUL_256_256_TEST_CASES.tests[0];
        let test_case = Modmul256BytesTestCase::from_raw(cs, &raw);

        // Performing the actual computation:
        let _ = test_case.a.modmul(cs, &test_case.b, &test_case.modulus);

        // Printing the number of constraints
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }
}
