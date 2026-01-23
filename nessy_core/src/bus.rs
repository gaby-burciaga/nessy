/// 2KiB of RAM.
pub const RAM_MEMORY_SIZE: usize = 2048;

pub const RAM_MEMORY_START: u16 = 0x0000;
pub const RAM_MEMORY_END: u16 = 0x2000;
pub const PRG_ROM_START: u16 = 0x8000;
pub const PRG_ROM_END: u16 = 0xFFFF;

pub const RESET_VECTOR_ADDR: u16 = 0xFFFC;
pub const INTERRUPT_VECTOR_ADDR: u16 = 0xFFFE;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bus {
    ram: Ram,
    prg_rom: Rom,
}

impl Bus {
    pub fn load(&mut self, prg_rom: Rom) {
        self.prg_rom = prg_rom;
        self.write_u16(RESET_VECTOR_ADDR, 0x8000);
    }

    pub fn read_u16(&self, addr: u16) -> u16 {
        let lo = self.read_u8(addr);
        let hi = self.read_u8(addr.wrapping_add(1));
        u16::from_le_bytes([lo, hi])
    }

    pub fn write_u16(&mut self, addr: u16, value: u16) {
        let [lo, hi] = value.to_le_bytes();
        self.write_u8(addr, lo);
        self.write_u8(addr.wrapping_add(1), hi);
    }

    pub fn read_u8(&self, addr: u16) -> u8 {
        match addr {
            RAM_MEMORY_START..RAM_MEMORY_END => self.ram.read_u8(addr),
            PRG_ROM_START..=PRG_ROM_END => self.prg_rom.read_u8(addr - PRG_ROM_START),
            _ => 0,
        }
    }

    pub fn write_u8(&mut self, addr: u16, value: u8) {
        match addr {
            RAM_MEMORY_START..RAM_MEMORY_END => self.ram.write_u8(addr, value),
            _ => {}
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ram {
    data: [u8; RAM_MEMORY_SIZE],
}

impl Ram {
    pub fn read_u8(&self, addr: u16) -> u8 {
        self.data[wrap_ram_addr(addr)]
    }

    pub fn write_u8(&mut self, addr: u16, value: u8) {
        self.data[wrap_ram_addr(addr)] = value;
    }
}

impl Default for Ram {
    fn default() -> Self {
        Ram {
            data: [0; RAM_MEMORY_SIZE],
        }
    }
}

/// Wraps a 16-bit address to the RAM size (2KiB).
/// Altough RAM is only 2KiB, the bus maps up to 8KiB, so we need to wrap around 0x07FF.
fn wrap_ram_addr(addr: u16) -> usize {
    (addr as usize) & 0x07FF
}
