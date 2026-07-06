use crate::{
    bus::Bus,
    cpu::{
        Cpu, CpuRegisters,
        instructions::{AddressingMode, INSTRUCTIONS},
    },
};

#[rustfmt::skip]
const OPCODE_NAMES: [&str;256] = [
    "BRK", "ORA", "???", "???", "???", "ORA", "ASL", "???", "PHP", "ORA", "ASL", "???", "???", "ORA", "ASL", "???", // 0x0_
    "BPL", "ORA", "???", "???", "???", "ORA", "ASL", "???", "CLC", "ORA", "???", "???", "???", "ORA", "ASL", "???", // 0x1_
    "JSR", "AND", "???", "???", "BIT", "AND", "ROL", "???", "PLP", "AND", "ROL", "???", "BIT", "AND", "ROL", "???", // 0x2_
    "BMI", "AND", "???", "???", "???", "AND", "ROL", "???", "SEC", "AND", "???", "???", "???", "AND", "ROL", "???", // 0x3_
    "RTI", "EOR", "???", "???", "???", "EOR", "LSR", "???", "PHA", "EOR", "LSR", "???", "JMP", "EOR", "LSR", "???", // 0x4_
    "BVC", "EOR", "???", "???", "???", "EOR", "LSR", "???", "CLI", "EOR", "???", "???", "???", "EOR", "LSR", "???", // 0x5_
    "RTS", "ADC", "???", "???", "???", "ADC", "ROR", "???", "PLA", "ADC", "ROR", "???", "JMP", "ADC", "ROR", "???", // 0x6_
    "BVS", "ADC", "???", "???", "???", "ADC", "ROR", "???", "SEI", "ADC", "???", "???", "???", "ADC", "ROR", "???", // 0x7_
    "???", "STA", "???", "???", "STY", "STA", "STX", "???", "DEY", "???", "TXA", "???", "STY", "STA", "STX", "???", // 0x8_
    "BCC", "STA", "???", "???", "STY", "STA", "STX", "???", "TYA", "STA", "TXS", "???", "???", "STA", "???", "???", // 0x9_
    "LDY", "LDA", "LDX", "???", "LDY", "LDA", "LDX", "???", "TAY", "LDA", "TAX", "???", "LDY", "LDA", "LDX", "???", // 0xA_
    "BCS", "LDA", "???", "???", "LDY", "LDA", "LDX", "???", "CLV", "LDA", "TSX", "???", "LDY", "LDA", "LDX", "???", // 0xB_
    "CPY", "CMP", "???", "???", "CPY", "CMP", "DEC", "???", "INY", "CMP", "DEX", "???", "CPY", "CMP", "DEC", "???", // 0xC_
    "BNE", "CMP", "???", "???", "???", "CMP", "DEC", "???", "CLD", "CMP", "???", "???", "???", "CMP", "DEC", "???", // 0xD_
    "CPX", "SBC", "???", "???", "CPX", "SBC", "INC", "???", "INX", "SBC", "NOP", "???", "CPX", "SBC", "INC", "???", // 0xE_
    "BEQ", "SBC", "???", "???", "???", "SBC", "INC", "???", "SED", "SBC", "???", "???", "???", "SBC", "INC", "???", // 0xF_
];

pub fn log_step(cpu: &Cpu, bus: &Bus) -> String {
    let regs = cpu.registers();
    let pc = regs.pc;

    let opcode = bus.read_u8(pc);
    let instruction = &INSTRUCTIONS[opcode as usize];
    let op_len = instruction.mode.operand_len();

    let b1 = if op_len >= 1 {
        bus.read_u8(pc.wrapping_add(1))
    } else {
        0
    };
    let b2 = if op_len >= 2 {
        bus.read_u8(pc.wrapping_add(2))
    } else {
        0
    };

    let raw = match op_len {
        0 => format!("{:02X}", opcode),
        1 => format!("{:02X} {:02X}", opcode, b1),
        2 => format!("{:02X} {:02X} {:02X}", opcode, b1, b2),
        _ => unreachable!(),
    };

    let name = OPCODE_NAMES[opcode as usize];
    let operand = format_operand(bus, &regs, instruction.mode, pc, name, b1, b2);
    let mnem = if operand.is_empty() {
        name.to_string()
    } else {
        format!("{} {}", name, operand)
    };

    format!(
        "{:04X}  {:<8}  {:<32}A:{:02X} X:{:02X} Y:{:02X} P:{:02X} SP:{:02X} PPU:{:>3},{:>3} CYC:{}",
        pc,
        raw,
        mnem,
        regs.acc,
        regs.x,
        regs.y,
        regs.status,
        regs.sp,
        0, // PPU scanline
        0, // PPU dot
        regs.cycles,
    )
}

fn format_operand(
    bus: &Bus,
    regs: &CpuRegisters,
    mode: AddressingMode,
    pc: u16,
    name: &str,
    b1: u8,
    b2: u8,
) -> String {
    let abs_addr = u16::from_le_bytes([b1, b2]);

    match mode {
        AddressingMode::Implied => String::new(),

        AddressingMode::Accumulator => "A".to_string(),

        AddressingMode::Immediate => format!("#${:02X}", b1),

        AddressingMode::ZeroPage => {
            let val = bus.read_u8(b1 as u16);
            format!("${:02X} = {:02X}", b1, val)
        }

        AddressingMode::ZeroPageX => {
            let ptr = b1.wrapping_add(regs.x);
            let val = bus.read_u8(ptr as u16);
            format!("${:02X},X @ {:02X} = {:02X}", b1, ptr, val)
        }

        AddressingMode::ZeroPageY => {
            let ptr = b1.wrapping_add(regs.y);
            let val = bus.read_u8(ptr as u16);
            format!("${:02X},Y @ {:02X} = {:02X}", b1, ptr, val)
        }

        AddressingMode::Relative => {
            // La dirección resuelta es relativa al PC *después* del fetch (pc + 2)
            let offset = b1 as i8;
            let target = (pc.wrapping_add(2) as i32 + offset as i32) as u16;
            format!("${:04X}", target)
        }

        AddressingMode::Absolute => {
            // JMP y JSR solo muestran la dirección, sin el valor en memoria
            if matches!(name, "JMP" | "JSR") {
                format!("${:04X}", abs_addr)
            } else {
                let val = bus.read_u8(abs_addr);
                format!("${:04X} = {:02X}", abs_addr, val)
            }
        }

        AddressingMode::AbsoluteX => {
            let effective = abs_addr.wrapping_add(regs.x as u16);
            let val = bus.read_u8(effective);
            format!("${:04X},X @ {:04X} = {:02X}", abs_addr, effective, val)
        }

        AddressingMode::AbsoluteY => {
            let effective = abs_addr.wrapping_add(regs.y as u16);
            let val = bus.read_u8(effective);
            format!("${:04X},Y @ {:04X} = {:02X}", abs_addr, effective, val)
        }

        AddressingMode::Indirect => {
            // Reproduce el bug del NMOS: high byte wrappea dentro de la misma página
            let lo = bus.read_u8(abs_addr);
            let hi_addr = (abs_addr & 0xFF00) | u16::from(abs_addr.wrapping_add(1) as u8);
            let hi = bus.read_u8(hi_addr);
            let target = u16::from_le_bytes([lo, hi]);
            format!("(${:04X}) = {:04X}", abs_addr, target)
        }

        AddressingMode::IndirectX => {
            let ptr = b1.wrapping_add(regs.x);
            let lo = bus.read_u8(ptr as u16);
            let hi = bus.read_u8(ptr.wrapping_add(1) as u16);
            let effective = u16::from_le_bytes([lo, hi]);
            let val = bus.read_u8(effective);
            format!(
                "(${:02X},X) @ {:02X} = {:04X} = {:02X}",
                b1, ptr, effective, val
            )
        }

        AddressingMode::IndirectY => {
            let lo = bus.read_u8(b1 as u16);
            let hi = bus.read_u8(b1.wrapping_add(1) as u16);
            let base = u16::from_le_bytes([lo, hi]);
            let effective = base.wrapping_add(regs.y as u16);
            let val = bus.read_u8(effective);
            format!(
                "(${:02X}),Y = {:04X} @ {:04X} = {:02X}",
                b1, base, effective, val
            )
        }
    }
}
