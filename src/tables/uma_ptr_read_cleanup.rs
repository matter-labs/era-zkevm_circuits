use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;

pub const UMA_PTR_READ_CLEANUP_TABLE_NAME: &'static str = "UMA PTR read cleanup mask table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UMAPtrReadCleanupTable;

pub fn create_uma_ptr_read_bitmask_table<F: SmallField>() -> LookupTable<F, 3> {
    let num_keys = 32;
    let mut all_keys = Vec::with_capacity(num_keys);
    for integer in 0..num_keys {
        let key = smallvec::smallvec![F::from_u64_unchecked(integer as u64)];
        all_keys.push(key);
    }

    const FULL_MASK: u64 = (1u64 << 32) - 1;

    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        UMA_PTR_READ_CLEANUP_TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced();

            let result = if a == 0 {
                FULL_MASK
            } else {
                let mut tmp = FULL_MASK;
                tmp -= (1u64 << a) - 1;

                tmp
            };

            smallvec::smallvec![F::from_u64_unchecked(result), F::ZERO]
        },
    )
}

#[cfg(test)]
mod tests {
    use boojum::field::goldilocks::GoldilocksField;

    use super::*;

    #[test]
    fn test_uma_table() {
        let table = create_uma_ptr_read_bitmask_table::<GoldilocksField>();

        let do_lookup = |key| {
            let (_position, result) =
                table.lookup_value::<2>(&[GoldilocksField::from_nonreduced_u64(key)]);
            result.iter().map(|x| x.0.clone()).collect::<Vec<u64>>()
        };

        assert_eq!(do_lookup(0), [0xffffffff, 0]);
        assert_eq!(do_lookup(1), [0xfffffffe, 0]);
        assert_eq!(do_lookup(2), [0xfffffffc, 0]);
        assert_eq!(do_lookup(4), [0xfffffff0, 0]);
        assert_eq!(do_lookup(8), [0xffffff00, 0]);
        assert_eq!(do_lookup(16), [0xffff0000, 0]);
        assert_eq!(do_lookup(31), [0x80000000, 0]);
    }
}
