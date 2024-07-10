use boojum::{
    config::DevCSConfig,
    cs::{
        cs_builder::{new_builder, CsBuilder, CsBuilderImpl},
        cs_builder_reference::CsReferenceImplementationBuilder,
        gates::{
            BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
            FmaGateInBaseFieldWithoutConstant, NopGate, ReductionGate, SelectionGate, U8x4FMAGate,
            UIntXAddGate, ZeroCheckGate,
        },
        implementations::reference_cs::CSReferenceImplementation,
        traits::{cs::ConstraintSystem, gate::GatePlacementStrategy},
        CSGeometry, GateConfigurationHolder, LookupParameters, StaticToolboxHolder,
    },
    field::{goldilocks::GoldilocksField, SmallField},
    gadgets::{
        non_native_field::implementations::NonNativeFieldOverU16Params,
        tables::{
            create_and8_table, create_byte_split_table, create_xor8_table, And8Table,
            ByteSplitTable, Xor8Table,
        },
    },
};

use crate::bn254::{
    fixed_base_mul_table::{create_fixed_base_mul_table, FixedBaseMulTable},
    BN256BaseNNFieldParams, BN256ScalarNNFieldParams,
};

type F = GoldilocksField;
type P = GoldilocksField;

/// Creates a test constraint system for testing purposes that includes the
/// majority (even possibly unneeded) of the gates and tables.
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
    let max_variables = 1 << 27;

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
                num_repetitions: 20,
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
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

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

/// Returns BN254 base field parameters
pub fn bn254_base_field_params() -> BN256BaseNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

/// Returns BN254 scalar field parameters
pub fn bn254_scalar_field_params() -> BN256ScalarNNFieldParams {
    NonNativeFieldOverU16Params::create()
}
