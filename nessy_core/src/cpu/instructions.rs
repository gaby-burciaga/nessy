use crate::{bus::Bus, cpu::Cpu};

/// Full 16x16 (256) instruction set for the 6502 CPU.
pub static INSTRUCTIONS: [Instruction; 256] = {
    let mut table = [Instruction::nop(); 256];

    table[0x01] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::IndirectX,
    };
    table[0x05] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::ZeroPage,
    };
    table[0x06] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::ZeroPage,
    };
    table[0x4C] = Instruction {
        exec: Cpu::jmp,
        mode: AddressingMode::Absolute,
    };
    table[0x09] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::Immediate,
    };
    table[0xA9] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::Immediate,
    };
    table[0xE8] = Instruction {
        exec: Cpu::inx,
        mode: AddressingMode::Implied,
    };
    table[0xAA] = Instruction {
        exec: Cpu::tax,
        mode: AddressingMode::Implied,
    };

    table
};

#[derive(Clone, Copy)]
pub struct Instruction {
    pub(super) exec: fn(&mut Cpu, &mut Bus, AddressingMode),
    pub(super) mode: AddressingMode,
}

impl Instruction {
    /// No operation instruction.
    const fn nop() -> Self {
        Instruction {
            exec: |_, _, _| {},
            mode: AddressingMode::Implied,
        }
    }
}
/// 6502 Addressing Modes.
#[derive(Clone, Copy)]
pub enum AddressingMode {
    Implied,
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Relative,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    IndirectX,
    IndirectY,
}
