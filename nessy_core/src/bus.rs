use crate::cartridge::Cartridge;

/// 2KiB of RAM.
pub const RAM_MEMORY_SIZE: usize = 2048;

pub const RAM_MEMORY_START: u16 = 0x0000;
pub const RAM_MEMORY_END: u16 = 0x2000;

pub const PPU_REGISTERS_START: u16 = 0x2000;
pub const PPU_REGISTERS_END: u16 = 0x4000;

pub const PRG_ROM_START: u16 = 0x8000;
pub const PRG_ROM_END: u16 = 0xFFFF;

pub const RESET_VECTOR_ADDR: u16 = 0xFFFC;
pub const INTERRUPT_VECTOR_ADDR: u16 = 0xFFFE;
pub const NMI_VECTOR_ADDR: u16 = 0xFFFA;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bus {
    ram: Ram,
    cartridge: Cartridge,
    ppu_registers: [u8; 8],
}

// TODO: Use proper logging instead of eprintln!

impl Bus {
    pub fn new(cartridge: Cartridge) -> Self {
        Bus {
            ram: Ram::default(),
            cartridge,
            ppu_registers: [0; 8],
        }
    }

    #[cfg(test)]
    pub fn load_test_rom(&mut self) {
        self.write_u16(RESET_VECTOR_ADDR, 0x8000);
    }

    pub fn read_u8(&self, addr: u16) -> u8 {
        match addr {
            RAM_MEMORY_START..RAM_MEMORY_END => self.ram.read_u8(addr),
            PPU_REGISTERS_START..PPU_REGISTERS_END => {
                // Stub: Returns the registers without any real side effects
                // TODO: Implement PPU register reading.
                let reg_index = (addr - PPU_REGISTERS_START) % 8;
                self.ppu_registers[reg_index as usize]
            }
            PRG_ROM_START..=PRG_ROM_END => {
                self.cartridge.prg_read_u8(addr.wrapping_sub(PRG_ROM_START))
            }
            _ => {
                #[cfg(debug_assertions)]
                {
                    eprintln!("Warning: Ingoring memory access at: {:#06X}", addr);
                }
                0
            }
        }
    }

    pub fn write_u8(&mut self, addr: u16, value: u8) {
        match addr {
            RAM_MEMORY_START..RAM_MEMORY_END => self.ram.write_u8(addr, value),
            PPU_REGISTERS_START..PPU_REGISTERS_END => {
                // Stub: Writes to the registers without any real side effects
                // TODO: Implement PPU register writing.
                let reg_index = (addr - PPU_REGISTERS_START) % 8;
                self.ppu_registers[reg_index as usize] = value;
            }
            PRG_ROM_START..=PRG_ROM_END => {
                #[cfg(debug_assertions)]
                {
                    eprintln!("Warning: Attempt to write to PRG ROM at: {:#06X}", addr);
                }
            }
            _ => {
                #[cfg(debug_assertions)]
                {
                    eprintln!("Warning: Ingoring memory write-access at: {:#06X}", addr);
                }
            }
        }
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
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ram {
    data: [u8; RAM_MEMORY_SIZE],
}

impl Ram {
    fn read_u8<Addr: Into<WrapRamAddr>>(&self, addr: Addr) -> u8 {
        self.data[addr.into().0 as usize]
    }

    fn write_u8<Addr: Into<WrapRamAddr>>(&mut self, addr: Addr, value: u8) {
        self.data[addr.into().0 as usize] = value;
    }
}

impl Default for Ram {
    fn default() -> Self {
        Ram {
            data: [0; RAM_MEMORY_SIZE],
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rom {
    data: Box<[u8]>,
}

impl Rom {
    pub fn new(data: Box<[u8]>) -> Self {
        Rom { data }
    }

    pub fn read_u8(&self, addr: u16) -> u8 {
        let index = addr as usize;
        self.data.get(index).copied().unwrap_or(0)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Wraps a 16-bit address to the RAM size (2KiB).
/// Altough RAM is only 2KiB, the bus maps up to 8KiB, so we need to wrap around 0x07FF by mirrowing.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct WrapRamAddr(u16);

impl WrapRamAddr {
    fn new(addr: u16) -> Self {
        WrapRamAddr(addr & 0x07FF)
    }
}

impl From<u16> for WrapRamAddr {
    fn from(addr: u16) -> Self {
        WrapRamAddr::new(addr)
    }
}
