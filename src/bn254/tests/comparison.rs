pub mod test {
    use crate::bn254::tests::json::TORUS_TEST_CASES;
    use crate::bn254::tests::utils::cs::create_test_cs;
    use boojum::field::goldilocks::GoldilocksField;
    use boojum::gadgets::tower_extension::algebraic_torus::TorusWrapper;

    type F = GoldilocksField;
    type P = GoldilocksField;

    /// Debugs the number of constraints for compressing the Torus element.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_torus_compression_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let _ = TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for compressing and then squaring the Torus element.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_torus_compress_and_square_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let mut scalar_1_torus = TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

        scalar_1_torus.square(cs);
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for squaring the Fq12 element.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_fq12_square_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let _ = scalar_1.square(cs);
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for compressing and then multiplying two Torus elements.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_torus_compress_and_mul_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 19);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let mut scalar_1_torus = TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

        let mut scalar_2 = test_case.scalar_2.to_fq12(cs);
        let mut scalar_2_torus = TorusWrapper::compress::<_, true>(cs, &mut scalar_2);

        let _ = scalar_1_torus.mul(cs, &mut scalar_2_torus);
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for squaring the Fq12 element.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_fq12_mul_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 19);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let mut scalar_2 = test_case.scalar_2.to_fq12(cs);

        let _ = scalar_1.mul(cs, &mut scalar_2);
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for compressing and then multiplying two Torus elements.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_torus_compress_and_pow_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let mut scalar_1_torus = TorusWrapper::compress::<_, true>(cs, &mut scalar_1);

        let _ = scalar_1_torus.pow_u32(cs, &[4965661367192848881]);
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }

    /// Debugs the number of constraints for squaring the Fq12 element.
    #[ignore = "For debugging (comparison) purposes only"]
    #[test]
    fn debug_fq12_pow_performance() {
        // Preparing the constraint system and parameters
        let mut owned_cs = create_test_cs(1 << 21);
        let cs = &mut owned_cs;

        let test_case = &TORUS_TEST_CASES.tests[0];
        let mut scalar_1 = test_case.scalar_1.to_fq12(cs);
        let _ = scalar_1.pow_u32(cs, &[4965661367192848881]);
        
        let cs = owned_cs.into_assembly::<std::alloc::Global>();
        cs.print_gate_stats();
    }
}
