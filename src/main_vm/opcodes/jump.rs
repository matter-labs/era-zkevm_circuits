use super::*;
use crate::base_structures::register::VMRegister;
use crate::boojum::gadgets::u256::UInt256;

pub(crate) fn apply_jump<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    _draft_vm_state: &VmLocalState<F>,
    common_opcode_state: &CommonOpcodeState<F>,
    opcode_carry_parts: &AfterDecodingCarryParts<F>,
    diffs_accumulator: &mut StateDiffsAccumulator<F>,
) {
    const JUMP_OPCODE: zkevm_opcode_defs::Opcode =
        zkevm_opcode_defs::Opcode::Jump(zkevm_opcode_defs::definitions::jump::JumpOpcode);

    let should_apply = common_opcode_state
        .decoded_opcode
        .properties_bits
        .boolean_for_opcode(JUMP_OPCODE);

    if crate::config::CIRCUIT_VERSOBE {
        if (should_apply.witness_hook(&*cs))().unwrap_or(false) {
            println!("Applying JUMP");
        }
    }

    // main point of merging add/sub is to enforce single add/sub relation, that doesn't leak into any
    // other opcodes

    let jump_dst = UInt16::from_le_bytes(
        cs,
        [
            common_opcode_state.src0_view.u8x32_view[0],
            common_opcode_state.src0_view.u8x32_view[1],
        ],
    );

    // save next_pc into dst0
    let boolean_false = Boolean::allocated_constant(cs, false);
    let mut saved_next_pc = UInt256::zero(cs);
    saved_next_pc.inner[0] =
        unsafe { UInt32::from_variable_unchecked(opcode_carry_parts.next_pc.get_variable()) };
    let dst0 = VMRegister {
        is_pointer: boolean_false,
        value: saved_next_pc,
    };
    let can_write_into_memory = JUMP_OPCODE.can_write_dst0_into_memory(SUPPORTED_ISA_VERSION);

    diffs_accumulator
        .new_pc_candidates
        .push((should_apply, jump_dst));

    diffs_accumulator
        .dst_0_values
        .push((can_write_into_memory, should_apply, dst0));
}
