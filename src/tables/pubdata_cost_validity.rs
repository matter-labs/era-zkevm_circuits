use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;

pub const VM_PUBDATA_COST_VALIDITY_TABLE_NAME: &'static str = "Pubdata cost validity table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PubdataCostValidityTable;

pub fn create_pubdata_cost_validity_table<F: SmallField>() -> LookupTable<F, 3> {
    let range = -65i8..=65i8;
    let num_rows = range.len();
    let mut all_keys = Vec::with_capacity(num_rows);

    for pubdata_cost_or_refund in range {
        let cost_as_u32 = (pubdata_cost_or_refund as i32) as u32;

        let sign_bit = pubdata_cost_or_refund < 0;
        let absolute_value = pubdata_cost_or_refund.abs() as u8 as u32;

        let row = [
            F::from_u64(cost_as_u32 as u64).unwrap(),
            F::from_u64(sign_bit as u64).unwrap(),
            F::from_u64(absolute_value as u64).unwrap(),
        ];

        all_keys.push(row);
    }

    assert_eq!(all_keys.len(), num_rows);

    LookupTable::new_from_content(all_keys, VM_PUBDATA_COST_VALIDITY_TABLE_NAME.to_string(), 1)
}
