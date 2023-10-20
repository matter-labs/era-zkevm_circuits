use boojum::algebraic_props::poseidon2_parameters::Poseidon2GoldilocksExternalMatrix;
use boojum::cs::gates::{
    BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
    FmaGateInBaseFieldWithoutConstant, MatrixMultiplicationGate, NopGate, ReductionGate,
    SelectionGate, UIntXAddGate, ZeroCheckGate,
};
use boojum::cs::implementations::reference_cs::{CSDevelopmentAssembly, CSReferenceImplementation};
use boojum::cs::traits::gate::GatePlacementStrategy;
use boojum::cs::CSGeometry;
use boojum::cs::*;
use boojum::field::goldilocks::GoldilocksField;
use boojum::field::Field;
use boojum::gadgets::tables::*;
use boojum::gadgets::traits::allocatable::CSPlaceholder;
use boojum::gadgets::traits::witnessable::WitnessHookable;
use boojum::implementations::poseidon2::Poseidon2Goldilocks;
use boojum::worker::Worker;

type F = GoldilocksField;
type P = GoldilocksField;

use boojum::config::*;
use boojum::cs::cs_builder::*;

// Add different boojum gates to the builder.
fn configure<T: CsBuilderImpl<F, T>, GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
    builder: CsBuilder<T, F, GC, TB>,
) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
    let owned_cs = builder;
    let owned_cs = owned_cs.allow_lookup(
        LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
            width: 3,
            num_repetitions: 8,
            share_table_id: true,
        },
    );
    let owned_cs = ConstantsAllocatorGate::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs = FmaGateInBaseFieldWithoutConstant::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs = ReductionGate::<F, 4>::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs = BooleanConstraintGate::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs = UIntXAddGate::<32>::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs = UIntXAddGate::<16>::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs =
        SelectionGate::configure_builder(owned_cs, GatePlacementStrategy::UseGeneralPurposeColumns);
    let owned_cs = ZeroCheckGate::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
        false,
    );
    let owned_cs = DotProductGate::<4>::configure_builder(
        owned_cs,
        GatePlacementStrategy::UseGeneralPurposeColumns,
    );
    let owned_cs =
        MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksExternalMatrix>::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
    let owned_cs =
        NopGate::configure_builder(owned_cs, GatePlacementStrategy::UseGeneralPurposeColumns);

    owned_cs
}

/// Create Boojum CS that includes almost all gates, and can be used in tets.
pub fn create_test_cs() -> CSReferenceImplementation<
    GoldilocksField,
    GoldilocksField,
    DevCSConfig,
    impl GateConfigurationHolder<GoldilocksField>,
    impl StaticToolboxHolder,
> {
    let geometry = CSGeometry {
        num_columns_under_copy_permutation: 100,
        num_witness_columns: 0,
        num_constant_columns: 8,
        max_allowed_constraint_degree: 4,
    };
    use boojum::config::DevCSConfig;
    use boojum::cs::cs_builder_reference::*;

    let builder_impl =
        CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, 1 << 26, 1 << 20);
    use boojum::cs::cs_builder::new_builder;
    let builder = new_builder::<_, F>(builder_impl);
    let builder = configure(builder);

    builder.build(())
}
