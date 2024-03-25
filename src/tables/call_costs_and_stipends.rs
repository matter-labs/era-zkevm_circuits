use super::*;
use boojum::cs::implementations::lookup_table::LookupTable;
use boojum::field::SmallField;
use zkevm_opcode_defs::NUM_SYSTEM_CONTRACTS;

pub const VM_CALL_COSTS_AND_STIPENDS_TABLE_NAME: &'static str = "Call costs and stipends table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallCostsAndStipendsTable;

pub fn create_call_costs_and_stipends_table<F: SmallField>() -> LookupTable<F, 3> {
    let mut all_keys = Vec::with_capacity(NUM_SYSTEM_CONTRACTS as usize);
    let num_rows = zkevm_opcode_defs::STIPENDS_AND_EXTRA_COSTS_TABLE.len();

    for address in 0..num_rows {
        let (caller_cost, stipend) = zkevm_opcode_defs::STIPENDS_AND_EXTRA_COSTS_TABLE[address];

        let row = [
            F::from_u64(address as u64).unwrap(),
            F::from_u64(caller_cost as u64).unwrap(),
            F::from_u64(stipend as u64).unwrap(),
        ];

        all_keys.push(row);
    }

    assert_eq!(all_keys.len(), num_rows);

    LookupTable::new_from_content(
        all_keys,
        VM_CALL_COSTS_AND_STIPENDS_TABLE_NAME.to_string(),
        1,
    )
}
