use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::field::SmallField;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::QueueTailState;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::u32::UInt32;

/// Creates challenges (random values) from state (seed) based on the state of these 2 queues (unsorted and sorted).
/// The first challenge from each repetition is 1 (TODO: check why..)
pub fn produce_fs_challenges<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, 8, 12, 4> + AlgebraicRoundFunction<F, 8, 12, 4>,
    const N: usize,
    const NUM_CHALLENGES: usize,
    const NUM_REPETITIONS: usize,
>(
    cs: &mut CS,
    unsorted_tail: QueueTailState<F, N>,
    sorted_tail: QueueTailState<F, N>,
    _round_function: &R,
) -> [[Num<F>; NUM_CHALLENGES]; NUM_REPETITIONS] {
    let mut fs_input = vec![];
    fs_input.extend_from_slice(&unsorted_tail.tail);
    fs_input.push(unsorted_tail.length.into_num());
    fs_input.extend_from_slice(&sorted_tail.tail);
    fs_input.push(sorted_tail.length.into_num());

    let mut state = R::create_empty_state(cs);
    let length = UInt32::allocated_constant(cs, fs_input.len() as u32);
    R::apply_length_specialization(cs, &mut state, length.get_variable());

    let zero_num = Num::allocated_constant(cs, F::ZERO);

    let mut state = state.map(|el| Num::from_variable(el));

    let mut it = fs_input.array_chunks::<8>();
    for chunk in &mut it {
        let mut state_to_keep = [zero_num; 4];
        state_to_keep.copy_from_slice(&state[8..]);
        state = R::absorb_with_replacement_over_nums(cs, *chunk, state_to_keep);
        state = R::compute_round_function_over_nums(cs, state);
    }

    let remainder = it.remainder();
    if remainder.len() != 0 {
        let mut state_to_keep = [zero_num; 4];
        state_to_keep.copy_from_slice(&state[8..]);
        let mut padded_chunk = [zero_num; 8];
        padded_chunk[..remainder.len()].copy_from_slice(remainder);
        state = R::absorb_with_replacement_over_nums(cs, padded_chunk, state_to_keep);
        state = R::compute_round_function_over_nums(cs, state);
    }

    // now get as many as necessary
    let max_to_take = 8;
    let mut can_take = max_to_take;

    let one_num = Num::allocated_constant(cs, F::ONE);

    let mut result = [[one_num; NUM_CHALLENGES]; NUM_REPETITIONS];

    for dst in result.iter_mut() {
        for dst in dst.iter_mut().skip(1) {
            if can_take == 0 {
                state = R::compute_round_function_over_nums(cs, state);
                can_take = max_to_take;
            }
            let el = state[max_to_take - can_take];
            can_take -= 1;
            *dst = el;
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use crate::test_utils::create_test_cs;

    use super::*;
    use boojum::algebraic_props::poseidon2_parameters::Poseidon2GoldilocksExternalMatrix;
    use boojum::cs::gates::{
        BooleanConstraintGate, ConstantsAllocatorGate, DotProductGate,
        FmaGateInBaseFieldWithoutConstant, MatrixMultiplicationGate, NopGate, ReductionGate,
        SelectionGate, UIntXAddGate, ZeroCheckGate,
    };
    use boojum::cs::implementations::reference_cs::{
        CSDevelopmentAssembly, CSReferenceImplementation,
    };
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

    #[test]
    fn test_challenge_generation() {
        let round_function = Poseidon2Goldilocks;

        let mut owned_cs = create_test_cs();

        let cs = &mut owned_cs;

        let empty_queue: QueueTailState<GoldilocksField, 4> = QueueTailState::placeholder(cs);

        let other_queue = QueueTailState {
            tail: [Num::allocated_constant(cs, F::ONE); 4],
            length: UInt32::allocated_constant(cs, 1),
        };

        let result = produce_fs_challenges::<_, _, _, 4, 10, 20>(
            cs,
            empty_queue,
            other_queue,
            &round_function,
        );
        // First element from each row should be equal to 1.
        assert_eq!(result[0][0].witness_hook(cs)().unwrap(), 1);
        assert_eq!(result[1][0].witness_hook(cs)().unwrap(), 1);
        assert_eq!(result[5][5].witness_hook(cs)().unwrap(), 0x72210b7b6f52fc72);

        // Result from arguments in different order, should create different challenges
        let result = produce_fs_challenges::<_, _, _, 4, 10, 20>(
            cs,
            other_queue,
            empty_queue,
            &round_function,
        );
        // First element from each row should be equal to 1.
        assert_eq!(result[0][0].witness_hook(cs)().unwrap(), 1);
        assert_eq!(result[1][0].witness_hook(cs)().unwrap(), 1);
        assert_eq!(result[5][5].witness_hook(cs)().unwrap(), 0x47aa7390d0f6fa01);
    }
}
