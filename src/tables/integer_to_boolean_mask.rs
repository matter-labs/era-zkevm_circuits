use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;

pub const REG_IDX_TO_BITMASK_TABLE_NAME: &'static str = "Register index to bitmask table";
pub const UMA_SHIFT_TO_BITMASK_TABLE_NAME: &'static str = "UMA shift to bitmask table";
pub const VM_SUBPC_TO_BITMASK_TABLE_NAME: &'static str = "Sub PC to bitmask table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterIndexToBitmaskTable;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UMAShiftToBitmaskTable;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VMSubPCToBitmaskTable;

pub fn create_integer_to_bitmask_table<F: SmallField>(
    num_bits: usize,
    name: &'static str,
) -> LookupTable<F, 3> {
    assert!(num_bits <= 16);
    let mut all_keys = Vec::with_capacity(1 << num_bits);
    for integer in 0..(1u64 << num_bits) {
        let key = smallvec::smallvec![F::from_u64_unchecked(integer as u64)];
        all_keys.push(key);
    }

    LookupTable::new_from_keys_and_generation_function(&all_keys, name.to_string(), 1, |keys| {
        let a = keys[0].as_u64_reduced();

        let result = if a == 0 {
            0u64
        } else {
            1u64 << (a - 1) // 1 in some position
        };

        smallvec::smallvec![F::from_u64_unchecked(result), F::ZERO]
    })
}

/// Creates a table of size 2^num_bits, with value [1<<x, 0] for each x.
pub fn create_integer_set_ith_bit_table<F: SmallField>(
    num_bits: usize,
    name: &'static str,
) -> LookupTable<F, 3> {
    assert!(num_bits <= 6);
    let mut all_keys = Vec::with_capacity(1 << num_bits);
    for integer in 0..(1u64 << num_bits) {
        let key = smallvec::smallvec![F::from_u64_unchecked(integer as u64)];
        all_keys.push(key);
    }

    LookupTable::new_from_keys_and_generation_function(&all_keys, name.to_string(), 1, |keys| {
        let a = keys[0].as_u64_reduced();

        let result = 1u64 << a; // 1 in some position

        smallvec::smallvec![F::from_u64_unchecked(result), F::ZERO]
    })
}

pub fn create_subpc_bitmask_table<F: SmallField>() -> LookupTable<F, 3> {
    create_integer_to_bitmask_table(2, VM_SUBPC_TO_BITMASK_TABLE_NAME)

    // let num_bits = 2;
    // let mut all_keys = Vec::with_capacity(1 << num_bits);
    // for integer in 0..(1u64 << num_bits) {
    //     let key = smallvec::smallvec![F::from_u64_unchecked(integer as u64)];
    //     all_keys.push(key);
    // }

    // LookupTable::new_from_keys_and_generation_function(
    //     &all_keys,
    //     VM_SUBPC_TO_BITMASK_TABLE_NAME.to_string(),
    //     1,
    //     |keys| {
    //         let a = keys[0].as_u64_reduced();

    //         let result = if a == 0 {
    //             0u64
    //         } else {
    //             1u64 << (a - 1) // 1 in some position
    //         };

    //         smallvec::smallvec![F::from_u64_unchecked(result), F::ZERO]
    //     },
    // )
}

#[cfg(test)]
mod tests {
    use boojum::field::goldilocks::GoldilocksField;

    use super::*;

    #[test]
    fn test_integer_set_ith() {
        let table = create_integer_set_ith_bit_table::<GoldilocksField>(6, "test");

        let do_lookup = |key| {
            let (_position, result) =
                table.lookup_value::<2>(&[GoldilocksField::from_nonreduced_u64(key)]);
            result.iter().map(|x| x.0.clone()).collect::<Vec<u64>>()
        };
        assert_eq!(do_lookup(0), [1, 0]);
        assert_eq!(do_lookup(1), [2, 0]);
        assert_eq!(do_lookup(3), [8, 0]);
        assert_eq!(do_lookup(63), [9223372036854775808, 0]);
    }
}
