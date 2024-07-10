pub mod test {
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::{new_builder, CsBuilder, CsBuilderImpl};
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::{
        BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
        FmaGateInBaseFieldWithoutConstant, ReductionGate, SelectionGate, UIntXAddGate,
    };
    use boojum::cs::implementations::reference_cs::CSReferenceImplementation;
    use boojum::cs::traits::cs::ConstraintSystem;
    use boojum::cs::traits::gate::GatePlacementStrategy;
    use boojum::cs::{CSGeometry, GateConfigurationHolder, LookupParameters, StaticToolboxHolder};
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::field::SmallField;
    use boojum::gadgets::tables::{
        create_and8_table, create_byte_split_table, create_xor8_table, And8Table, ByteSplitTable,
        Xor8Table,
    };

    use crate::bn254::ec_add::implementation::projective_add;
    use crate::bn254::fixed_base_mul_table::{create_fixed_base_mul_table, FixedBaseMulTable};
    use crate::bn254::tests::json::EC_ADD_TEST_CASES;
    use crate::bn254::tests::utils::assert::assert_equal_g1_points;
    use crate::bn254::tests::utils::debug_success;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Creates a test constraint system for testing purposes
    pub fn create_ecadd_cs(
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
            let builder = DotProductGate::<4>::configure_builder(
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

        seq_macro::seq!(C in 0..32 {
            let table = create_fixed_base_mul_table::<F, 0, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<0, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 1, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<1, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 2, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<2, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 3, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<3, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 4, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<4, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 5, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<5, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 6, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<6, C>, 3>(table);
            let table = create_fixed_base_mul_table::<F, 7, C>();
            owned_cs.add_lookup_table::<FixedBaseMulTable<7, C>, 3>(table);
        });

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

    #[test]
    fn test_addition() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_ecadd_cs(1 << 21);
        let cs = &mut owned_cs;

        // Runnings tests from file
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in EC_ADD_TEST_CASES.tests.iter().enumerate() {
            // Expected:
            let mut expected_sum = test.expected.to_projective_point(cs);

            // Actual:
            let mut point_1 = test.point_1.to_projective_point(cs);
            let (x, y) = test.point_2.to_coordinates(cs);
            let mut sum = projective_add(cs, &mut point_1, (x, y));

            assert_equal_g1_points(cs, &mut sum, &mut expected_sum);

            debug_success("ec_add", i, DEBUG_FREQUENCY);
        }
    }

    #[test]
    #[ignore = "used for debugging performance"]
    fn debug_ecadd_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_ecadd_cs(1 << 21);
        let cs = &mut owned_cs;

        // Runnings test
        let test_case = &EC_ADD_TEST_CASES.tests[0];

        let mut point_1 = test_case.point_1.to_projective_point(cs);
        let (x, y) = test_case.point_2.to_coordinates(cs);
        let _ = projective_add(cs, &mut point_1, (x, y));

        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }
}
