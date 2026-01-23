#![allow(dead_code)]

use crate::{
    bus::{Bus, INTERRUPT_VECTOR_ADDR, RESET_VECTOR_ADDR},
    cpu::instructions::{AddressingMode, INSTRUCTIONS},
};

use bitflags::bitflags;

pub mod instructions;

const STACK_RESET: u8 = 0xFD;

pub struct Cpu {
    /// Program Counter.
    pc: u16,
    /// Stack Pointer.
    sp: u8,
    /// Accumulator.
    acc: u8,
    /// X Register.
    x: u8,
    /// Y Register.
    y: u8,
    /// N V _ B D I Z C
    status: Status,
}

bitflags! {
    /// Processor Status Flags.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Status: u8 {
        /// Carry Flag.
        const C = (1 << 0);
        /// Zero Flag.
        const Z = (1 << 1);
        /// Interrupt Disable.
        const I = (1 << 2);
        /// Decimal Mode Flag.
        const D = (1 << 3);
        /// Break Command.
        const B = (1 << 4);
        /// Unused.
        const U = (1 << 5);
        /// Overflow Flag.
        const V = (1 << 6);
        /// Negative Flag.
        const N = (1 << 7);
    }
}

impl Default for Cpu {
    fn default() -> Self {
        Cpu {
            pc: 0,
            sp: STACK_RESET,
            acc: 0,
            x: 0,
            y: 0,
            status: Status::from_bits_truncate(0b100100),
        }
    }
}

impl Cpu {
    /// Executes a single CPU step (fetch-decode-execute cycle).
    pub fn step(&mut self, bus: &mut Bus) {
        let opscode = bus.read_u8(self.pc);
        self.pc += 1;

        let instruction = &INSTRUCTIONS[opscode as usize];
        dbg!("Executing instruction: {:02X?}", opscode);
        (instruction.exec)(self, bus, instruction.mode);
    }

    pub fn reset(&mut self, bus: &mut Bus) {
        self.acc = 0;
        self.x = 0;
        self.y = 0;

        self.sp = STACK_RESET;
        self.pc = bus.read_u16(RESET_VECTOR_ADDR);
        self.status = Status::from_bits_truncate(0b100100);
    }

    pub fn load(&mut self, bus: &mut Bus) {
        self.pc = bus.read_u16(RESET_VECTOR_ADDR);
        self.reset(bus);
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

                (self.pc as i32 + offset as i32) as u16
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

    /// Force Break.
    fn brk(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let [lo, hi] = self.pc.wrapping_add(1).to_le_bytes();
        self.push(bus, hi);
        self.push(bus, lo);

        let mut status = self.status;
        status.insert(Status::B | Status::U);
        self.push(bus, status.bits());

        self.status.insert(Status::I);

        self.pc = bus.read_u16(INTERRUPT_VECTOR_ADDR);
    }

    /// Logical Inclusive OR.
    fn ora(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc |= value;
        self.set_zn(self.acc);
    }

    /// Arithmetic Shift Left.
    fn asl(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::Accumulator => {
                let carry = self.acc & (1 << 7) != 0;
                self.acc <<= 1;
                (self.acc, carry)
            }
            _ => {
                let addr = self.get_operand_address(bus, mode);
                let mut value = bus.read_u8(addr);

                let carry = value & (1 << 7) != 0;
                value <<= 1;

                bus.write_u8(addr, value);

                (value, carry)
            }
        };

        self.status.set(Status::C, carry);
        self.set_zn(result);
    }

    /// Push Processor Status.
    fn php(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let mut status = self.status;
        status.insert(Status::U | Status::B);
        self.push(bus, status.bits());
    }

    /// Branch If Plus.
    fn bpl(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if !self.status.contains(Status::N) {
            self.pc = addr;
        }
    }

    /// Clear Carry Flag.
    fn clc(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.remove(Status::C);
    }

    /// Jump to Subroutine.
    fn jsr(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let return_addr = self.pc.wrapping_sub(1);
        let [lo, hi] = return_addr.to_le_bytes();
        self.push(bus, hi);
        self.push(bus, lo);
        self.pc = addr;
    }

    /// Logical AND.
    fn and(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc &= value;
        self.set_zn(self.acc);
    }

    /// Bit Test.
    fn bit(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = self.acc & value;

        self.status.remove(Status::N | Status::V);
        self.status
            .insert(Status::from_bits_truncate(value & (0b1100_0000)));
        self.status.set(Status::Z, result == 0);
    }

    /// Rotate Left.
    fn rol(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::Accumulator => {
                let (r, carry) = self._rol(self.acc);
                self.acc = r;
                (r, carry)
            }
            _ => {
                let addr = self.get_operand_address(bus, mode);
                let value = bus.read_u8(addr);

                let (r, carry) = self._rol(value);
                bus.write_u8(addr, r);

                (r, carry)
            }
        };

        self.status.set(Status::C, carry);
        self.set_zn(result);
    }

    fn _rol(&self, value: u8) -> (u8, bool) {
        let carry = value & (1 << 7) != 0;
        let mut result = value << 1;
        result |= self.status.bits() & 1;
        (result, carry)
    }

    /// Pull Processor Status.
    fn plp(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let mut status = Status::from_bits_truncate(self.pull(bus));
        status.remove(Status::B);
        status.insert(Status::U);
        self.status = status;
    }

    /// Branch on Minus.
    fn bmi(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if self.status.contains(Status::N) {
            self.pc = addr;
        }
    }

    /// Set Carry Flag.
    fn sec(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.insert(Status::C);
    }

    /// Return from Interrupt.
    fn rti(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let mut status = Status::from_bits_truncate(self.pull(bus));
        status.remove(Status::B);
        status.insert(Status::U);
        self.status = status;

        let lo = self.pull(bus);
        let hi = self.pull(bus);
        self.pc = u16::from_le_bytes([lo, hi]);
    }

    /// Exclusive OR.
    fn eor(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc ^= value;
        self.set_zn(self.acc);
    }

    /// Logical Shift Right.
    fn lsr(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::Accumulator => {
                let (r, carry) = self._lsr(self.acc);
                self.acc = r;
                (r, carry)
            }
            _ => {
                let addr = self.get_operand_address(bus, mode);
                let value = bus.read_u8(addr);
                let (result, carry) = self._lsr(value);

                bus.write_u8(addr, result);
                (result, carry)
            }
        };

        self.status.set(Status::C, carry);
        self.set_zn(result);
    }

    fn _lsr(&self, value: u8) -> (u8, bool) {
        let carry = value & 1 != 0;
        let result = value >> 1;
        (result, carry)
    }

    /// Push Accumulator.
    fn pha(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        self.push(bus, self.acc);
    }

    /// Branch If Overflow Clear.
    fn bvc(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if !self.status.contains(Status::V) {
            self.pc = addr;
        }
    }

    /// Clear Interrupt Disable.
    fn cli(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.remove(Status::I);
    }

    /// Return from Subroutine.
    fn rts(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let lo = self.pull(bus);
        let hi = self.pull(bus);
        let return_addr = u16::from_le_bytes([lo, hi]).wrapping_add(1);
        self.pc = return_addr;
    }

    /// Add with Carry.
    fn adc(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self._adc(value);
    }

    fn _adc(&mut self, value: u8) {
        let carry_in = self.status.bits() & 1;
        let (sum1, carry1) = self.acc.overflowing_add(value);
        let (sum2, carry2) = sum1.overflowing_add(carry_in);

        // See http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        // basically, overflow occurs if the sign of the two inputs is the same but
        // the sign of the result is different.
        // + + = - overflow
        // - - = + overflow
        // + - = + no overflow
        // - + = - no overflow
        let overflow = (self.acc ^ sum2) & (value ^ sum2) & 0x80 != 0;

        self.acc = sum2;

        self.status.set(Status::V, overflow);
        self.status.set(Status::C, carry1 || carry2);

        self.set_zn(self.acc);
    }

    /// Rotate Right.
    fn ror(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let (result, carry) = match mode {
            AddressingMode::Accumulator => {
                let (r, carry) = self._ror(self.acc);
                self.acc = r;
                (r, carry)
            }
            _ => {
                let addr = self.get_operand_address(bus, mode);
                let value = bus.read_u8(addr);

                let (r, carry) = self._ror(value);
                bus.write_u8(addr, r);

                (r, carry)
            }
        };

        self.status.set(Status::C, carry);
        self.set_zn(result);
    }

    fn _ror(&mut self, value: u8) -> (u8, bool) {
        let carry = value & 1 != 0;
        let mut result = value >> 1;
        result |= (self.status.bits() & 1) << 7;
        (result, carry)
    }

    /// Pull Accumulator.
    fn pla(&mut self, bus: &mut Bus, _mode: AddressingMode) {
        let acc = self.pull(bus);
        self.acc = acc;
        self.set_zn(self.acc);
    }

    /// Jump to Address.
    fn jmp(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        self.pc = addr;
    }

    /// Branch If Overflow Clear.
    fn bvs(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if self.status.contains(Status::V) {
            self.pc = addr;
        }
    }

    /// Set Interrupt Disable.
    fn sei(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.insert(Status::I);
    }

    /// Store Accumulator.
    fn sta(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        bus.write_u8(addr, self.acc);
    }

    /// Store Y Register.
    fn sty(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        bus.write_u8(addr, self.y);
    }

    /// Store X Register.
    fn stx(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        bus.write_u8(addr, self.x);
    }

    /// Decrement Y Register.
    fn dey(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.y = self.y.wrapping_sub(1);
        self.set_zn(self.y);
    }

    /// Transfer X to Accumulator.
    fn txa(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.acc = self.x;
        self.set_zn(self.acc);
    }

    /// Branch If Carry Clear.
    fn bcc(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if !self.status.contains(Status::C) {
            self.pc = addr;
        }
    }

    /// Transfer Y to Accumulator.
    fn tya(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.acc = self.y;
        self.set_zn(self.acc);
    }

    /// Transfer X to Stack Pointer.
    fn txs(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.sp = self.x;
    }

    /// Load Accumulator.
    fn ldy(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.y = value;
        self.set_zn(self.y);
    }

    /// Load X Register.
    fn lda(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc = value;
        self.set_zn(self.acc);
    }

    /// Load X Register.
    fn ldx(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.x = value;
        self.set_zn(self.x);
    }

    /// Transfer Accumulator to Y.
    fn tay(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.y = self.acc;
        self.set_zn(self.y);
    }

    /// Transfer Accumulator to X.
    fn tax(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.acc;
        self.set_zn(self.x);
    }

    /// Branch If Carry Set.
    fn bcs(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if self.status.contains(Status::C) {
            self.pc = addr;
        }
    }

    /// Subtract with Carry.
    fn sbc(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self._adc(!value);
    }

    /// Compare Accumulator.
    fn cmp(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = self.acc.wrapping_sub(value);
        self.status.set(Status::C, self.acc >= value);
        self.set_zn(result);
    }

    /// Clear Overflow Flag.
    fn clv(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.remove(Status::V);
    }

    /// Transfer Stack Pointer to X.
    fn tsx(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.sp;
        self.set_zn(self.x);
    }

    /// Compare Y Register.
    fn cpy(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = self.y.wrapping_sub(value);
        self.status.set(Status::C, self.y >= value);
        self.set_zn(result);
    }

    /// Decrement Memory.
    fn dec(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = value.wrapping_sub(1);
        bus.write_u8(addr, result);
        self.set_zn(result);
    }

    /// Increment Y Register.
    fn iny(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.y = self.y.wrapping_add(1);
        self.set_zn(self.y);
    }

    /// Decrement X Register.
    fn dex(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.x.wrapping_sub(1);
        self.set_zn(self.x);
    }

    /// Branch If Not Equal (Zero).
    fn bne(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if !self.status.contains(Status::Z) {
            self.pc = addr;
        }
    }

    /// Clear Decimal Mode.
    fn cld(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.status.remove(Status::D);
    }

    /// Compare X Register.
    fn cpx(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = self.x.wrapping_sub(value);
        self.status.set(Status::C, self.x >= value);
        self.set_zn(result);
    }

    /// Increment X Register.
    fn inx(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.x.wrapping_add(1);
        self.set_zn(self.x);
    }

    /// Increment Memory.
    fn inc(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);

        let result = value.wrapping_add(1);
        bus.write_u8(addr, result);
        self.set_zn(result);
    }

    /// Branch on Result Zero (Equal).
    fn beq(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);

        if self.status.contains(Status::Z) {
            self.pc = addr;
        }
    }

    /// Pushes a byte onto the stack.
    fn push(&mut self, bus: &mut Bus, value: u8) {
        bus.write_u8(0x0100 | self.sp as u16, value);
        self.sp = self.sp.wrapping_sub(1);
    }

    /// Pulls a byte from the stack.
    fn pull(&mut self, bus: &mut Bus) -> u8 {
        self.sp = self.sp.wrapping_add(1);
        let byte = bus.read_u8(0x0100 | self.sp as u16);
        byte
    }

    /// Sets the Zero and Negative flags based on the given value.
    fn set_zn(&mut self, value: u8) {
        self.status.set(Status::Z, value == 0);
        self.status.set(Status::N, value & 0x80 != 0);
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
