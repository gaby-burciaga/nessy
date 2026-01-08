#![allow(dead_code)]

static INSTRUCTIONS: [Instruction; 256] = {
    let mut table = [Instruction::nop(); 256];

    table[0x01] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::IndirectX,
    };
    table[0x05] = Instruction {
        exec: Cpu::ora,
        mode: AddressingMode::ZeroPage,
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
        mode: AddressingMode::Immediate,
    };
    table[0xAA] = Instruction {
        exec: Cpu::tax,
        mode: AddressingMode::Immediate,
    };

    table
};

pub struct Bus {
    ram: Ram,
    prg_rom: Rom,
}

impl Bus {
    pub fn new(prg_rom: Rom) -> Self {
        Bus {
            ram: Ram::default(),
            prg_rom,
        }
    }

    pub fn read_u16(&self, addr: u16) -> u16 {
        let lo = self.read_u8(addr);
        let hi = self.read_u8(addr + 1);
        u16::from_le_bytes([lo, hi])
    }

    pub fn write_u16(&mut self, addr: u16, value: u16) {
        let lo = (value & 0x00FF) as u8;
        let hi = (value >> 8) as u8;
        self.write_u8(addr, lo);
        self.write_u8(addr + 1, hi);
    }

    pub fn read_u8(&self, addr: u16) -> u8 {
        match addr {
            0x0000..0x2000 => self.ram.read_u8(addr),
            0x8000..=0xFFFF => self.prg_rom.read_u8(addr - 0x8000),
            _ => 0,
        }
    }

    pub fn write_u8(&mut self, addr: u16, value: u8) {
        match addr {
            0x0000..0x2000 => self.ram.write_u8(addr, value),
            _ => {}
        }
    }
}

pub struct Rom {
    data: Vec<u8>,
}

impl Rom {
    pub fn new(data: Vec<u8>) -> Self {
        Rom { data }
    }

    pub fn read_u8(&self, addr: u16) -> u8 {
        let index = addr as usize;
        self.data.get(index).copied().unwrap_or(0)
    }
}

/// 2KiB of RAM.
const MEMORY_SIZE: usize = 2048;

pub struct Ram {
    data: [u8; MEMORY_SIZE],
}

impl Ram {
    pub fn read_u8(&self, addr: u16) -> u8 {
        self.data[ram_mask(addr)]
    }

    pub fn write_u8(&mut self, addr: u16, value: u8) {
        self.data[ram_mask(addr)] = value;
    }
}

fn ram_mask(addr: u16) -> usize {
    (addr as usize) & 0x07FF
}

impl Default for Ram {
    fn default() -> Self {
        Ram {
            data: [0; MEMORY_SIZE],
        }
    }
}

#[derive(Default)]
pub struct Cpu {
    pc: u16,
    sp: u8,
    acc: u8,
    x: u8,
    y: u8,
    /// N V _ B D I Z C
    status: u8,
}

impl Cpu {
    fn interpret(&mut self, bus: &mut Bus) {
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
            AddressingMode::Immediate => {
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
                addr + self.x as u16
            }
            AddressingMode::ZeroPageY => {
                let addr = bus.read_u8(self.pc) as u16;
                self.pc += 1;
                addr + self.y as u16
            }
            AddressingMode::Absolute => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr
            }
            AddressingMode::AbsoluteX => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr
            }
            AddressingMode::AbsoluteY => {
                let addr = bus.read_u16(self.pc);
                self.pc += 2;
                addr
            }
            _ => todo!(),
        }
    }

    fn ora(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc |= value;
        self.update_zero_and_negative_flags(self.acc);
    }

    fn lda(&mut self, bus: &mut Bus, mode: AddressingMode) {
        let addr = self.get_operand_address(bus, mode);
        let value = bus.read_u8(addr);
        self.acc = value;
        self.update_zero_and_negative_flags(self.acc);
    }

    fn inx(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x += 1;
        self.update_zero_and_negative_flags(self.x);
    }

    fn tax(&mut self, _bus: &mut Bus, _mode: AddressingMode) {
        self.x = self.acc;
        self.update_zero_and_negative_flags(self.x);
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

#[derive(Clone, Copy)]
enum AddressingMode {
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

#[derive(Clone, Copy)]
struct Instruction {
    exec: fn(&mut Cpu, &mut Bus, AddressingMode),
    mode: AddressingMode,
}

impl Instruction {
    const fn nop() -> Self {
        Instruction {
            exec: |_, _, _| {},
            mode: AddressingMode::Immediate,
        }
    }
}

#[cfg(test)]
mod tests {
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
