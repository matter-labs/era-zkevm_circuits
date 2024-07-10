pub mod test {
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder::{new_builder, CsBuilder, CsBuilderImpl};
    use boojum::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use boojum::cs::gates::{
        BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
        FmaGateInBaseFieldWithoutConstant, ReductionGate, SelectionGate, U8x4FMAGate, UIntXAddGate,
        ZeroCheckGate,
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

    use crate::bn254::ec_mul::implementation::{
        width_4_windowed_multiplication, ScalarDecomposition,
    };
    use crate::bn254::fixed_base_mul_table::{create_fixed_base_mul_table, FixedBaseMulTable};
    use crate::bn254::tests::json::{DECOMPOSITION_TEST_CASES, EC_MUL_TEST_CASES};
    use crate::bn254::tests::utils::assert::assert_equal_g1_points;
    use crate::bn254::tests::utils::debug_success;
    use crate::bn254::{
        bn254_base_field_params, bn254_scalar_field_params, BN256Fr, BN256ScalarNNField,
    };
    use boojum::gadgets::traits::witnessable::WitnessHookable;
    use boojum::pairing::ff::PrimeField;
    use std::sync::Arc;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Creates a test constraint system for testing purposes
    pub fn create_ecmul_cs(
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
    fn test_scalar_decomposition() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_ecmul_cs(1 << 21);
        let cs = &mut owned_cs;
        let scalar_params = Arc::new(bn254_scalar_field_params());

        // Running tests from file
        const DEBUG_FREQUENCY: usize = 10;
        for (i, test) in DECOMPOSITION_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let k = BN256Fr::from_str(&test.k).unwrap();
            let mut k = BN256ScalarNNField::allocate_checked(cs, k, &scalar_params);

            // Expected:
            let expected_k1 = BN256Fr::from_str(&test.k1).unwrap();
            let expected_k2 = BN256Fr::from_str(&test.k2).unwrap();

            // Actual:
            let decomposition = ScalarDecomposition::from(cs, &mut k, &scalar_params);
            let k1 = decomposition.k1.witness_hook(cs)().unwrap().get();
            let k1_was_negated = decomposition.k1_was_negated.witness_hook(cs)().unwrap();
            let k2 = decomposition.k2.witness_hook(cs)().unwrap().get();
            let k2_was_negated = decomposition.k2_was_negated.witness_hook(cs)().unwrap();

            // Asserting:
            assert_eq!(k1, expected_k1);
            assert_eq!(k1_was_negated, test.k1_negated);
            assert_eq!(k2, expected_k2);
            assert_eq!(k2_was_negated, test.k2_negated);

            debug_success("decomposition", i, DEBUG_FREQUENCY);
        }
    }

    #[test]
    fn test_width_4_multiplication() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_ecmul_cs(1 << 21);
        let cs = &mut owned_cs;
        let scalar_params = Arc::new(bn254_scalar_field_params());
        let base_params = Arc::new(bn254_base_field_params());

        // Running tests from file
        const DEBUG_FREQUENCY: usize = 2;
        for (i, test) in EC_MUL_TEST_CASES.tests.iter().enumerate() {
            // Input:
            let point_nn = test.point.to_projective_point(cs);
            let scalar = BN256Fr::from_str(&test.scalar).unwrap();
            let scalar_nn = BN256ScalarNNField::allocate_checked(cs, scalar, &scalar_params);

            // Expected:
            let mut expected = test.expected.to_projective_point(cs);

            // Actual:
            let mut actual = width_4_windowed_multiplication(
                cs,
                point_nn,
                scalar_nn,
                &base_params,
                &scalar_params,
            );

            // Making assertion and debug success if OK
            assert_equal_g1_points(cs, &mut actual, &mut expected);
            debug_success("ec_mul", i, DEBUG_FREQUENCY);
        }
    }

    #[test]
    #[ignore = "used for debugging performance"]
    fn debug_ecmul_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_ecmul_cs(1 << 21);
        let cs = &mut owned_cs;

        // Preparing params
        let scalar_params = Arc::new(bn254_scalar_field_params());
        let base_params = Arc::new(bn254_base_field_params());

        // Runnings test
        let test_case = &EC_MUL_TEST_CASES.tests[0];
        let point_nn = test_case.point.to_projective_point(cs);
        let scalar = BN256Fr::from_str(&test_case.scalar).unwrap();
        let scalar_nn = BN256ScalarNNField::allocate_checked(cs, scalar, &scalar_params);

        let _ =
            width_4_windowed_multiplication(cs, point_nn, scalar_nn, &base_params, &scalar_params);

        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }
}
