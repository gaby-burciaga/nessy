use crate::{
    bus::Bus,
    cpu::instructions::{AddressingMode, INSTRUCTIONS},
};

pub mod instructions;

#[derive(Default)]
pub struct Cpu {
    pc: u16,
    _sp: u8,
    acc: u8,
    x: u8,
    y: u8,
    /// N V _ B D I Z C
    status: u8,
}

impl Cpu {
    pub fn interpret(&mut self, bus: &mut Bus) {
        self.pc = 0x8000;

        loop {
            let opscode = bus.read_u8(self.pc);
            self.pc += 1;

            if opscode == 0x00 {
                break;
            }

            let instruction = INSTRUCTIONS[opscode as usize];
            (instruction.exec)(self, bus, instruction.mode);
        }
    }

    fn get_operand_address(&mut self, bus: &mut Bus, mode: AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate | AddressingMode::Accumulator => {
                let addr = self.pc;
                self.pc += 1;
                addr
            }
            AddressingMode::ZeroPage => {
                let addr = bus.read_u8(self.pc) as u16;
                self.pc += 1;
                addr
            }
            AddressingMode::ZeroPageX => {
                let addr = bus.read_u8(self.pc) as u16;
                self.pc += 1;
                wrap_zero_page(addr.wrapping_add(self.x as u16))
            }
            AddressingMode::ZeroPageY => {
                let addr = bus.read_u8(self.pc) as u16;
                self.pc += 1;
                wrap_zero_page(addr.wrapping_add(self.y as u16))
            }
            AddressingMode::Relative => {
                let offset = bus.read_u8(self.pc) as i8;
                self.pc += 1;

                if !offset.is_negative() {
                    self.pc.wrapping_add(offset as u16)
                } else {
                    self.pc.wrapping_sub((-offset) as u16)
                }
            }
            AddressingMode::Absolute => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr
            }
            AddressingMode::AbsoluteX => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr.wrapping_add(self.x as u16)
            }
            AddressingMode::AbsoluteY => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr.wrapping_add(self.y as u16)
            }
            AddressingMode::Indirect => {
                // Reproducing JMP $xxFF bug by wrapping around the page
                let ptr = bus.read_u16(self.pc);
                self.pc += 2;
                let lo = bus.read_u8(ptr);
                let hi = bus.read_u8(wrap_around_page(ptr));
                u16::from_le_bytes([lo, hi])
            }
            AddressingMode::IndirectX => {
                let addr = bus.read_u8(self.pc);
                self.pc += 1;

                let ptr = addr.wrapping_add(self.x);
                let lo = bus.read_u8(ptr as u16);
                let hi = bus.read_u8(ptr.wrapping_add(1) as u16);

                u16::from_le_bytes([lo, hi])
            }
            AddressingMode::IndirectY => {
                let addr = bus.read_u8(self.pc);
                self.pc += 1;

                let lo = bus.read_u8(addr as u16);
                let hi = bus.read_u8(addr.wrapping_add(1) as u16);
                let ptr = u16::from_le_bytes([lo, hi]);

                ptr.wrapping_add(self.y as u16)
            }
            AddressingMode::Implied => panic!("Instruction should not request addr"),
        }
    }

    fn ora(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc |= value;
        self.update_zero_and_negative_flags(self.acc);
    }

    fn asl(&mut self, bus: &mut Bus, mode: AddressingMode) {
        match mode {
            AddressingMode::Accumulator => {
                let carry = self.acc & (1 << 7) != 0;
                self.acc <<= 1;

                self.set_carry(carry);
                self.update_zero_and_negative_flags(self.acc);
            }
            _ => {
                let addr = self.get_operand_address(bus, mode);
                let mut value = bus.read_u8(addr);

                let carry = value & (1 << 7) != 0;
                value <<= 1;

                bus.write_u8(addr, value);

                self.set_carry(carry);
                self.update_zero_and_negative_flags(value);
            }
        }
    }

    fn set_carry(&mut self, carry: bool) {
        if carry {
            self.status |= 1;
        } else {
            self.status &= !1;
        }
    }

    fn lda(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc = value;
        self.update_zero_and_negative_flags(self.acc);
    }

    fn inx(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        let _ = self.x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.x);
    }

    fn tax(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.acc;
        self.update_zero_and_negative_flags(self.x);
    }

    fn jmp(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        self.pc = addr;
    }

    fn update_zero_and_negative_flags(&mut self, value: u8) {
        if value == 0 {
            self.status |= 0b0000_0010;
        } else {
            self.status &= 0b1111_1101;
        }

        if value & 0b1000_0000 != 0 {
            self.status |= 0b1000_0000;
        } else {
            self.status &= 0b0111_1111;
        }
    }
}

/// Wraps a 16-bit address to the zero page (0x00 to 0xFF).
fn wrap_zero_page(addr: u16) -> u16 {
    addr & 0x00FF
}

fn wrap_around_page(addr: u16) -> u16 {
    let page = addr & 0xFF00;
    let offset = (addr + 1) & 0x00FF;
    page | offset
}

// TODO: Test addressing modes and instructions more thoroughly.

#[cfg(test)]
mod tests {
    use crate::bus::Rom;

    use super::*;

    #[test]
    fn test_lda_immediate() {
        let prg_rom = Rom::new(vec![0xA9, 0x42, 0x00]); // LDA #$42; BRK
        let mut bus = Bus::new(prg_rom);
        let mut cpu = Cpu::default();

        cpu.interpret(&mut bus);

        assert_eq!(cpu.acc, 0x42);
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }
}
