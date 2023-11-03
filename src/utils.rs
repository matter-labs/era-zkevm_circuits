use boojum::algebraic_props::round_function::AlgebraicRoundFunction;
use boojum::cs::traits::cs::ConstraintSystem;
use boojum::cs::Variable;
use boojum::field::SmallField;
use boojum::gadgets::boolean::Boolean;
use boojum::gadgets::num::Num;
use boojum::gadgets::queue::QueueTailState;
use boojum::gadgets::traits::round_function::CircuitRoundFunction;
use boojum::gadgets::traits::selectable::Selectable;
use boojum::gadgets::u32::UInt32;

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

// Strange signature of the function is due to const generics bugs
pub fn accumulate_grand_products<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const ENCODING_LENGTH: usize,
    const NUM_CHALLENGES: usize,
    const NUM_REPETITIONS: usize,
>(
    cs: &mut CS,
    lhs_accumulator: &mut [Num<F>; NUM_REPETITIONS],
    rhs_accumulator: &mut [Num<F>; NUM_REPETITIONS],
    fs_challenges: &[[Num<F>; NUM_CHALLENGES]; NUM_REPETITIONS],
    lhs_encoding: &[Variable; ENCODING_LENGTH],
    rhs_encoding: &[Variable; ENCODING_LENGTH],
    should_accumulate: Boolean<F>,
) {
    assert!(ENCODING_LENGTH > 0);
    assert_eq!(ENCODING_LENGTH + 1, NUM_CHALLENGES);
    for ((challenges, lhs), rhs) in fs_challenges
        .iter()
        .zip(lhs_accumulator.iter_mut())
        .zip(rhs_accumulator.iter_mut())
    {
        // additive parts
        let mut lhs_contribution = challenges[ENCODING_LENGTH];
        let mut rhs_contribution = challenges[ENCODING_LENGTH];

        for ((lhs_el, rhs_el), challenge) in lhs_encoding
            .iter()
            .zip(rhs_encoding.iter())
            .zip(challenges.iter())
        {
            lhs_contribution = Num::fma(
                cs,
                &Num::from_variable(*lhs_el),
                challenge,
                &F::ONE,
                &lhs_contribution,
                &F::ONE,
            );

            rhs_contribution = Num::fma(
                cs,
                &Num::from_variable(*rhs_el),
                challenge,
                &F::ONE,
                &rhs_contribution,
                &F::ONE,
            );
        }

        let new_lhs = lhs.mul(cs, &lhs_contribution);
        let new_rhs = rhs.mul(cs, &rhs_contribution);

        *lhs = Num::conditionally_select(cs, should_accumulate, &new_lhs, &lhs);
        *rhs = Num::conditionally_select(cs, should_accumulate, &new_rhs, &rhs);
    }
}
