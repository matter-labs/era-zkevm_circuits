pub mod test {
    use std::fs::File;
    use std::io::Read;
    use std::sync::Arc;

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
    use boojum::field::SmallField;
    use boojum::gadgets::boolean::Boolean;
    use boojum::gadgets::modexp::{modexp, modmul};
    use boojum::gadgets::tables::{
        create_and8_table, create_byte_split_table, create_xor8_table, And8Table, ByteSplitTable,
        Xor8Table,
    };
    use boojum::gadgets::u256::UInt256;
    use lazy_static::lazy_static;
    use serde::{Deserialize, Serialize};

    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::curves::sw_projective::SWProjectivePoint;
    use boojum::gadgets::traits::witnessable::WitnessHookable;
    use boojum::pairing::ff::{Field, PrimeField};

    use crate::modexp::tests_json::{
        ModexpTestCase, ModmulTestCase, MODEXP_TEST_CASES, MODMUL_TEST_CASES,
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

    /// This function tests the modular exponentiation
    #[test]
    fn test_modexp() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODEXP_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = ModexpTestCase::from_raw(cs, &raw);

            // Expected:
            let actual_modexp = modexp(cs, &test.base, &test.exponent, &test.modulus);

            // Actual:
            let expected_modexp = test.expected.clone();

            // Asserting
            assert_equal_uint256(cs, &actual_modexp, &expected_modexp);
        }
    }

    /// This function tests the modular multiplication
    #[test]
    fn test_modmul() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        // Running tests from file
        for (_, raw) in MODMUL_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let test = ModmulTestCase::from_raw(cs, &raw);

            // Expected:
            let actual_modmul = modmul(cs, &test.a, &test.b, &test.modulus);

            // Actual:
            let expected_modmul = test.expected.clone();

            // Asserting
            assert_equal_uint256(cs, &actual_modmul, &expected_modmul);
        }
    }
}
