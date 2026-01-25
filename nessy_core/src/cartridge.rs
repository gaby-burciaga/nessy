use std::{fs, path::Path};

use crate::bus::Rom;

/// 16 KiB
const PRG_PAGE_SIZE: usize = 16 * 1024;
/// 8 KiB
const CHR_PAGE_SIZE: usize = 8 * 1024;

const NES_TAG: &[u8; 4] = b"NES\x1A";

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Cartridge {
    pub prg_rom: Rom,
    pub chr_rom: Rom,
    pub mapper_type: u8,
    pub screen_mirrowing: ScreenMirrowing,
}

impl Cartridge {
    pub fn from_raw(data: &[u8]) -> Self {
        check_nes_tag(&data);
        check_ines_version(&data);

        let prg_rom_size = data[4] as usize * PRG_PAGE_SIZE;
        let chr_rom_size = data[5] as usize * CHR_PAGE_SIZE;

        let hi = data[7] & 0xF0;
        let lo = data[6] >> 4;
        let mapper_type = hi | lo;

        let four_screen = data[6] & (1 << 3) != 0;
        let vertical_mirrowing = data[6] & 1 != 0;

        let screen_mirrowing = match (four_screen, vertical_mirrowing) {
            (true, _) => ScreenMirrowing::FourScreen,
            (false, true) => ScreenMirrowing::Vertical,
            (false, false) => ScreenMirrowing::Horizontal,
        };

        let skip_trainer = data[6] & (1 << 2) != 0;

        let prg_rom_start = 16 + if skip_trainer { 512 } else { 0 };
        let chr_rom_start = prg_rom_start + prg_rom_size;

        Cartridge {
            prg_rom: Rom::new(
                data[prg_rom_start..prg_rom_start + prg_rom_size]
                    .to_vec()
                    .into_boxed_slice(),
            ),
            chr_rom: Rom::new(
                data[chr_rom_start..chr_rom_start + chr_rom_size]
                    .to_vec()
                    .into_boxed_slice(),
            ),
            mapper_type,
            screen_mirrowing,
        }
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Self {
        let data = fs::read(path).expect("Cartridge file");
        Self::from_raw(&data)
    }

    pub fn prg_read_u8(&self, addr: u16) -> u8 {
        self.prg_rom.read_u8(addr % self.prg_rom.len() as u16)
    }

    pub fn chr_read_u8(&self, _addr: u16) -> u8 {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScreenMirrowing {
    Horizontal,
    Vertical,
    FourScreen,
}

fn check_nes_tag(data: &[u8]) {
    assert!(&data[0..4] == NES_TAG, "Invalid NES file: Missing NES tag");
}

fn check_ines_version(data: &[u8]) {
    let ines_ver = data[7] >> 2 & 0x03;
    assert!(ines_ver == 0, "Only iNES format version 0 is supported");
}
