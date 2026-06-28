use crate::{bus::Bus, cpu::Cpu};

// TODO: Implement illegal opcodes?

/// Full 16x16 (256) instruction set for the 6502 CPU.
pub static INSTRUCTIONS: [Instruction; 256] = {
    let mut table = [Instruction::nop(); 256];

    table[0x00] = Instruction {
        exec: Cpu::brk,
        mode: AddressingMode::Implied,
        cycles: 7,
    };
    table[0x01] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0x02] = Instruction::nop();
    table[0x03] = Instruction::nop();
    table[0x04] = Instruction::nop();
    table[0x05] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x06] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0x07] = Instruction::nop();
    table[0x08] = Instruction {
        exec: Cpu::php,
        mode: AddressingMode::Implied,
        cycles: 3,
    };
    table[0x09] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0x0A] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::Accumulator,
        cycles: 2,
    };
    table[0x0B] = Instruction::nop();
    table[0x0C] = Instruction::nop();
    table[0x0D] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x0E] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0x0F] = Instruction::nop();

    table[0x10] = Instruction {
        exec: Cpu::bpl,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0x11] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0x12] = Instruction::nop();
    table[0x13] = Instruction::nop();
    table[0x14] = Instruction::nop();
    table[0x15] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x16] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0x17] = Instruction::nop();
    table[0x18] = Instruction {
        exec: Cpu::clc,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x19] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0x1A] = Instruction::nop();
    table[0x1B] = Instruction::nop();
    table[0x1C] = Instruction::nop();
    table[0x1D] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0x1E] = Instruction {
        exec: Cpu::asl,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0x1F] = Instruction::nop();
    table[0x20] = Instruction {
        exec: Cpu::jsr,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0x21] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0x22] = Instruction::nop();
    table[0x23] = Instruction::nop();
    table[0x24] = Instruction {
        exec: Cpu::bit,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x25] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x26] = Instruction {
        exec: Cpu::rol,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0x27] = Instruction::nop();
    table[0x28] = Instruction {
        exec: Cpu::plp,
        mode: AddressingMode::Implied,
        cycles: 4,
    };
    table[0x29] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0x2A] = Instruction {
        exec: Cpu::rol,
        mode: AddressingMode::Accumulator,
        cycles: 2,
    };
    table[0x2B] = Instruction::nop();
    table[0x2C] = Instruction {
        exec: Cpu::bit,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x2D] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x2E] = Instruction {
        exec: Cpu::rol,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0x2F] = Instruction::nop();

    table[0x30] = Instruction {
        exec: Cpu::bmi,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0x31] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0x32] = Instruction::nop();
    table[0x33] = Instruction::nop();
    table[0x34] = Instruction::nop();
    table[0x35] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x36] = Instruction {
        exec: Cpu::rol,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0x37] = Instruction::nop();
    table[0x38] = Instruction {
        exec: Cpu::sec,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x39] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0x3A] = Instruction::nop();
    table[0x3B] = Instruction::nop();
    table[0x3C] = Instruction::nop();
    table[0x3D] = Instruction {
        exec: Cpu::and,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0x3E] = Instruction {
        exec: Cpu::rol,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0x3F] = Instruction::nop();
    table[0x40] = Instruction {
        exec: Cpu::rti,
        mode: AddressingMode::Implied,
        cycles: 6,
    };
    table[0x41] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0x42] = Instruction::nop();
    table[0x43] = Instruction::nop();
    table[0x44] = Instruction::nop();
    table[0x45] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x46] = Instruction {
        exec: Cpu::lsr,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0x47] = Instruction::nop();
    table[0x48] = Instruction {
        exec: Cpu::pha,
        mode: AddressingMode::Implied,
        cycles: 3,
    };
    table[0x49] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0x4A] = Instruction {
        exec: Cpu::lsr,
        mode: AddressingMode::Accumulator,
        cycles: 2,
    };
    table[0x4B] = Instruction::nop();
    table[0x4C] = Instruction {
        exec: Cpu::jmp,
        mode: AddressingMode::Absolute,
        cycles: 3,
    };
    table[0x4D] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x4E] = Instruction {
        exec: Cpu::lsr,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0x4F] = Instruction::nop();
    table[0x50] = Instruction {
        exec: Cpu::bvc,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0x51] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0x52] = Instruction::nop();
    table[0x53] = Instruction::nop();
    table[0x54] = Instruction::nop();
    table[0x55] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x56] = Instruction {
        exec: Cpu::lsr,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0x57] = Instruction::nop();
    table[0x58] = Instruction {
        exec: Cpu::cli,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x59] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0x5A] = Instruction::nop();
    table[0x5B] = Instruction::nop();
    table[0x5C] = Instruction::nop();
    table[0x5D] = Instruction {
        exec: Cpu::eor,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0x5E] = Instruction {
        exec: Cpu::lsr,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0x5F] = Instruction::nop();
    table[0x60] = Instruction {
        exec: Cpu::rts,
        mode: AddressingMode::Implied,
        cycles: 6,
    };
    table[0x61] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0x62] = Instruction::nop();
    table[0x63] = Instruction::nop();
    table[0x64] = Instruction::nop();
    table[0x65] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x66] = Instruction {
        exec: Cpu::ror,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0x67] = Instruction::nop();
    table[0x68] = Instruction {
        exec: Cpu::pla,
        mode: AddressingMode::Implied,
        cycles: 4,
    };
    table[0x69] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0x6A] = Instruction {
        exec: Cpu::ror,
        mode: AddressingMode::Accumulator,
        cycles: 2,
    };
    table[0x6B] = Instruction::nop();
    // FIX: What???
    table[0x6C] = Instruction {
        exec: Cpu::jmp,
        mode: AddressingMode::Indirect,
        cycles: 5,
    };
    table[0x6D] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x6E] = Instruction {
        exec: Cpu::ror,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0x6F] = Instruction::nop();
    table[0x70] = Instruction {
        exec: Cpu::bvs,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0x71] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0x72] = Instruction::nop();
    table[0x73] = Instruction::nop();
    table[0x74] = Instruction::nop();
    table[0x75] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x76] = Instruction {
        exec: Cpu::ror,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0x77] = Instruction::nop();
    table[0x78] = Instruction {
        exec: Cpu::sei,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x79] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0x7A] = Instruction::nop();
    table[0x7B] = Instruction::nop();
    table[0x7C] = Instruction::nop();
    table[0x7D] = Instruction {
        exec: Cpu::adc,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0x7E] = Instruction {
        exec: Cpu::ror,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0x7F] = Instruction::nop();
    table[0x80] = Instruction::nop();
    table[0x81] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0x82] = Instruction::nop();
    table[0x83] = Instruction::nop();
    table[0x84] = Instruction {
        exec: Cpu::sty,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x85] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x86] = Instruction {
        exec: Cpu::stx,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0x87] = Instruction::nop();
    table[0x88] = Instruction {
        exec: Cpu::dey,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x89] = Instruction::nop();
    table[0x8A] = Instruction {
        exec: Cpu::txa,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x8B] = Instruction::nop();
    table[0x8C] = Instruction {
        exec: Cpu::sty,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x8D] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x8E] = Instruction {
        exec: Cpu::stx,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0x8F] = Instruction::nop();
    table[0x90] = Instruction {
        exec: Cpu::bcc,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0x91] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::IndirectY,
        cycles: 6,
    };
    table[0x92] = Instruction::nop();
    table[0x93] = Instruction::nop();
    table[0x94] = Instruction {
        exec: Cpu::sty,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x95] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0x96] = Instruction {
        exec: Cpu::stx,
        mode: AddressingMode::ZeroPageY,
        cycles: 4,
    };
    table[0x97] = Instruction::nop();
    table[0x98] = Instruction {
        exec: Cpu::tya,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x99] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::AbsoluteY,
        cycles: 5,
    };
    table[0x9A] = Instruction {
        exec: Cpu::txs,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0x9B] = Instruction::nop();
    table[0x9C] = Instruction::nop();
    table[0x9D] = Instruction {
        exec: Cpu::sta,
        mode: AddressingMode::AbsoluteX,
        cycles: 5,
    };
    table[0x9E] = Instruction::nop();
    table[0x9F] = Instruction::nop();
    table[0xA0] = Instruction {
        exec: Cpu::ldy,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xA1] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0xA2] = Instruction {
        exec: Cpu::ldx,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xA3] = Instruction::nop();
    table[0xA4] = Instruction {
        exec: Cpu::ldy,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xA5] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xA6] = Instruction {
        exec: Cpu::ldx,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xA7] = Instruction::nop();
    table[0xA8] = Instruction {
        exec: Cpu::tay,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xA9] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xAA] = Instruction {
        exec: Cpu::tax,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xAB] = Instruction::nop();
    table[0xAC] = Instruction {
        exec: Cpu::ldy,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xAD] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xAE] = Instruction {
        exec: Cpu::ldx,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xAF] = Instruction::nop();
    table[0xB0] = Instruction {
        exec: Cpu::bcs,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0xB1] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0xB2] = Instruction::nop();
    table[0xB3] = Instruction::nop();
    table[0xB4] = Instruction {
        exec: Cpu::ldy,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0xB5] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0xB6] = Instruction {
        exec: Cpu::ldx,
        mode: AddressingMode::ZeroPageY,
        cycles: 4,
    };
    table[0xB7] = Instruction::nop();
    table[0xB8] = Instruction {
        exec: Cpu::clv,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xB9] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0xBA] = Instruction {
        exec: Cpu::tsx,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xBB] = Instruction::nop();
    table[0xBC] = Instruction {
        exec: Cpu::ldy,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0xBD] = Instruction {
        exec: Cpu::lda,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0xBE] = Instruction {
        exec: Cpu::ldx,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0xBF] = Instruction::nop();
    table[0xC0] = Instruction {
        exec: Cpu::cpy,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xC1] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0xC2] = Instruction::nop();
    table[0xC3] = Instruction::nop();
    table[0xC4] = Instruction {
        exec: Cpu::cpy,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xC5] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xC6] = Instruction {
        exec: Cpu::dec,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0xC7] = Instruction::nop();
    table[0xC8] = Instruction {
        exec: Cpu::iny,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xC9] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xCA] = Instruction {
        exec: Cpu::dex,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xCB] = Instruction::nop();
    table[0xCC] = Instruction {
        exec: Cpu::cpy,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xCD] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xCE] = Instruction {
        exec: Cpu::dec,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0xCF] = Instruction::nop();
    table[0xD0] = Instruction {
        exec: Cpu::bne,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0xD1] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0xD2] = Instruction::nop();
    table[0xD3] = Instruction::nop();
    table[0xD4] = Instruction::nop();
    table[0xD5] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0xD6] = Instruction {
        exec: Cpu::dec,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0xD7] = Instruction::nop();
    table[0xD8] = Instruction {
        exec: Cpu::cld,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xD9] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0xDA] = Instruction::nop();
    table[0xDB] = Instruction::nop();
    table[0xDC] = Instruction::nop();
    table[0xDD] = Instruction {
        exec: Cpu::cmp,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0xDE] = Instruction {
        exec: Cpu::dec,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0xDF] = Instruction::nop();
    table[0xE0] = Instruction {
        exec: Cpu::cpx,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xE1] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::IndirectX,
        cycles: 6,
    };
    table[0xE2] = Instruction::nop();
    table[0xE3] = Instruction::nop();
    table[0xE4] = Instruction {
        exec: Cpu::cpx,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xE5] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::ZeroPage,
        cycles: 3,
    };
    table[0xE6] = Instruction {
        exec: Cpu::inc,
        mode: AddressingMode::ZeroPage,
        cycles: 5,
    };
    table[0xE7] = Instruction::nop();
    table[0xE8] = Instruction {
        exec: Cpu::inx,
        mode: AddressingMode::Implied,
        cycles: 2,
    };
    table[0xE9] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::Immediate,
        cycles: 2,
    };
    table[0xEA] = Instruction::nop();
    table[0xEB] = Instruction::nop();
    table[0xEC] = Instruction {
        exec: Cpu::cpx,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xED] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::Absolute,
        cycles: 4,
    };
    table[0xEE] = Instruction {
        exec: Cpu::inc,
        mode: AddressingMode::Absolute,
        cycles: 6,
    };
    table[0xEF] = Instruction::nop();
    table[0xF0] = Instruction {
        exec: Cpu::beq,
        mode: AddressingMode::Relative,
        cycles: 2,
    };
    table[0xF1] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::IndirectY,
        cycles: 5,
    };
    table[0xF2] = Instruction::nop();
    table[0xF3] = Instruction::nop();
    table[0xF4] = Instruction::nop();
    table[0xF5] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::ZeroPageX,
        cycles: 4,
    };
    table[0xF6] = Instruction {
        exec: Cpu::inc,
        mode: AddressingMode::ZeroPageX,
        cycles: 6,
    };
    table[0xF7] = Instruction::nop();
    // SED, not implemented in NES
    table[0xF8] = Instruction::nop();
    table[0xF9] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::AbsoluteY,
        cycles: 4,
    };
    table[0xFA] = Instruction::nop();
    table[0xFB] = Instruction::nop();
    table[0xFC] = Instruction::nop();
    table[0xFD] = Instruction {
        exec: Cpu::sbc,
        mode: AddressingMode::AbsoluteX,
        cycles: 4,
    };
    table[0xFE] = Instruction {
        exec: Cpu::inc,
        mode: AddressingMode::AbsoluteX,
        cycles: 7,
    };
    table[0xFF] = Instruction::nop();

    table
};

/// 6502 Instruction.
#[derive(Clone, Copy)]
pub struct Instruction {
    pub(super) exec: fn(&mut Cpu, &mut Bus, AddressingMode),
    pub(super) mode: AddressingMode,
    pub(super) cycles: u8,
}

impl Instruction {
    /// No operation instruction.
    const fn nop() -> Self {
        Instruction {
            exec: |_, _, _| {},
            mode: AddressingMode::Implied,
            cycles: 2,
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
