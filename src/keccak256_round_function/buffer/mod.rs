use super::*;
use crate::boojum::gadgets::traits::auxiliary::PrettyComparison;
use crate::boojum::serde_utils::BigArraySerde;

#[derive(Derivative, CSAllocatable, CSSelectable, CSVarLengthEncodable, WitnessHookable)]
#[derivative(Clone, Copy, Debug)]
#[DerivePrettyComparison("true")]
pub struct ByteBuffer<F: SmallField, const BUFFER_SIZE: usize> {
    pub bytes: [UInt8<F>; BUFFER_SIZE],
    pub filled: UInt8<F>, // assume that it's enough
}

impl<F: SmallField, const BUFFER_SIZE: usize> CSPlaceholder<F> for ByteBuffer<F, BUFFER_SIZE> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_u8 = UInt8::zero(cs);
        Self {
            bytes: [zero_u8; BUFFER_SIZE],
            filled: zero_u8,
        }
    }
}

// we map a set of offset + current fill factor into "start from here" bit for 0-th byte of the buffer of length N
pub type BufferMappingFunction<F, CS, const N: usize, const M: usize> =
    fn(&mut CS, UInt8<F>, UInt8<F>, [(); N]) -> [Boolean<F>; M];

impl<F: SmallField, const BUFFER_SIZE: usize> ByteBuffer<F, BUFFER_SIZE> {
    pub fn can_fill_fixed_bytes<CS: ConstraintSystem<F>, const N: usize>(
        &self,
        cs: &mut CS,
    ) -> Boolean<F> {
        let max_filled = BUFFER_SIZE - N;
        let max_filled = u8::try_from(max_filled).expect("must fit into u8");
        let upper_bound = UInt8::allocate_constant(cs, max_filled);
        // we need to check that filled <= max_filled
        let (_, uf) = upper_bound.overflowing_sub(cs, &self.filled);
        let can_fill = uf.negated(cs);

        can_fill
    }

    pub fn can_fill_bytes<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        bytes_to_fill: UInt8<F>,
    ) -> Boolean<F> {
        let next_filled = self.filled.add_no_overflow(cs, bytes_to_fill);
        let max_filled = BUFFER_SIZE;
        let max_filled = u8::try_from(max_filled).expect("must fit into u8");
        let upper_bound = UInt8::allocate_constant(cs, max_filled);
        // we need to check that next_filled <= max_filled
        let (_, uf) = upper_bound.overflowing_sub(cs, &next_filled);
        let can_fill = uf.negated(cs);

        can_fill
    }

    pub fn can_consume_n_bytes<CS: ConstraintSystem<F>, const N: usize>(
        &self,
        cs: &mut CS,
    ) -> Boolean<F> {
        let bytes_to_consume = N;
        let bytes_to_consume = u8::try_from(bytes_to_consume).expect("must fit into u8");
        let bytes_to_consume = UInt8::allocate_constant(cs, bytes_to_consume);
        // we need to check that filled >= bytes_to_consume
        let (_, uf) = self.filled.overflowing_sub(cs, &bytes_to_consume);
        let can_consume = uf.negated(cs);

        can_consume
    }

    // must be called only after caller ensures enough capacity left
    pub fn fill_with_bytes<CS: ConstraintSystem<F>, const N: usize>(
        &mut self,
        cs: &mut CS,
        input: &[UInt8<F>; N],
        offset: UInt8<F>,
        meaningful_bytes: UInt8<F>,
        mapping_function: BufferMappingFunction<F, CS, N, BUFFER_SIZE>,
    ) {
        // we do naive implementation of the shift register
        let mut offset = offset.into_num();
        let one_num = Num::allocated_constant(cs, F::ONE);
        let zero_u8 = UInt8::zero(cs);
        // base case
        let mut shifted_input = *input;
        offset = offset.sub(cs, &one_num);
        for i in 1..N {
            let use_form_here = offset.is_zero(cs);
            offset = offset.sub(cs, &one_num);
            let mut candidate = [zero_u8; N];
            candidate[0..(N - i)].copy_from_slice(&input[i..]);
            shifted_input = <[UInt8<F>; N]>::conditionally_select(
                cs,
                use_form_here,
                &candidate,
                &shifted_input,
            );
        }
        // now we can use a mapping function to determine based on the number of meaningful bytes and current fill factor
        // on which bytes to use from the start and which not. We already shifted all meaningful bytes to the left above,
        // so we only need 1 bit to show "start here"

        // dbg!(shifted_input.witness_hook(cs)());

        let use_byte_for_place_mask = mapping_function(cs, meaningful_bytes, self.filled, [(); N]);
        // TODO: transpose to use linear combination
        for (idx, src) in shifted_input.into_iter().enumerate() {
            // buffer above is shifted all the way to the left, so if byte number 0 can use any of 0..BUFFER_SIZE markers,
            // then for byte number 1 we can only use markers 1..BUFFER_SIZE markers, and so on, and byte number 1 can never go into
            // buffer position 0
            let markers = &use_byte_for_place_mask[..(BUFFER_SIZE - idx)];
            let dsts = &mut self.bytes[idx..];
            assert_eq!(markers.len(), dsts.len());

            for (dst, flag) in dsts.iter_mut().zip(markers.iter()) {
                *dst = UInt8::conditionally_select(cs, *flag, &src, &*dst);
            }
        }
        self.filled = self.filled.add_no_overflow(cs, meaningful_bytes);
        // compare no overflow
        let capacity = u8::try_from(BUFFER_SIZE).expect("must fit into u8");
        let _ = UInt8::allocated_constant(cs, capacity).sub_no_overflow(cs, self.filled);
    }

    pub fn consume<CS: ConstraintSystem<F>, const N: usize>(
        &mut self,
        cs: &mut CS,
        allow_partial: Boolean<F>,
    ) -> [UInt8<F>; N] {
        let bytes_to_take = u8::try_from(N).expect("must fit");
        let bytes_to_take = UInt8::allocated_constant(cs, bytes_to_take);
        let (leftover, uf) = self.filled.overflowing_sub(cs, &bytes_to_take);
        let have_enough = uf.negated(cs);
        let is_valid = Boolean::multi_or(cs, &[have_enough, allow_partial]);
        let boolean_true = Boolean::allocated_constant(cs, true);
        Boolean::enforce_equal(cs, &is_valid, &boolean_true);

        self.filled = leftover.mask_negated(cs, uf);

        let zero_u8 = UInt8::zero(cs);
        let mut result = [zero_u8; N];
        result.copy_from_slice(&self.bytes[..N]);

        let mut new_bytes = [zero_u8; BUFFER_SIZE];
        new_bytes[..(BUFFER_SIZE - N)].copy_from_slice(&self.bytes[N..]);

        self.bytes = new_bytes;

        result
    }
}
