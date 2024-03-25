use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;

pub const TEST_BIT_TABLE_NAME: &'static str = "Test bit table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TestBitTable;

pub fn create_test_bit_table<F: SmallField>() -> LookupTable<F, 3> {
    // we put u8 word in the first element, and bit index (starting from 0) in the second element,
    // and get 0/1 as a result
    let num_rows = (1 << 8) * 8;
    let mut all_keys = Vec::with_capacity(num_rows);

    for byte_value in 0..256 {
        for bit_idx in 0..8 {
            let key = smallvec::smallvec![
                F::from_u64_unchecked(byte_value as u64),
                F::from_u64_unchecked(bit_idx as u64)
            ];
            all_keys.push(key);
        }
    }

    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TEST_BIT_TABLE_NAME.to_string(),
        2,
        |keys| {
            let byte = keys[0].as_u64_reduced();
            let bit_index = keys[1].as_u64_reduced();

            let result = if byte & (1 << bit_index) == 0 {
                0u64
            } else {
                1u64
            };

            smallvec::smallvec![F::from_u64_unchecked(result)]
        },
    )
}
