use std::sync::{Arc, Mutex};

use eframe::egui::{self, Color32, RichText};
use nessy_core::{
    bus::Bus,
    cartridge::Cartridge,
    cpu::{Cpu, CpuRegisters},
};

/// ~29,780 cycles per frame at 60Hz (1/60 seconds per frame)
const CYCLES_PER_FRAME: u32 = 29_780;

struct EmulatorState {
    cpu: Cpu,
    bus: Bus,
}

impl EmulatorState {
    fn new(cartridge: Cartridge) -> Self {
        let mut bus = Bus::new(cartridge);
        let mut cpu = Cpu::default();
        cpu.reset(&mut bus);
        EmulatorState { cpu, bus }
    }

    fn step(&mut self) {
        self.cpu.step(&mut self.bus);
    }

    fn step_frame(&mut self) {
        for _ in 0..CYCLES_PER_FRAME {
            self.cpu.step(&mut self.bus);
        }
    }

    fn reset(&mut self) {
        self.cpu.reset(&mut self.bus);
    }

    fn registers(&self) -> CpuRegisters {
        self.cpu.registers()
    }
}

pub struct NessyApp {
    state: Option<EmulatorState>,
    running: bool,
    error: Option<String>,
    rom_bytes_rx: Arc<Mutex<Option<Vec<u8>>>>,
}

impl Default for NessyApp {
    fn default() -> Self {
        NessyApp {
            state: None,
            running: false,
            error: None,
            rom_bytes_rx: Arc::new(Mutex::new(None)),
        }
    }
}

impl eframe::App for NessyApp {
    fn ui(&mut self, ui: &mut eframe::egui::Ui, _frame: &mut eframe::Frame) {
        let bytes = if let Ok(mut lock) = self.rom_bytes_rx.lock() {
            lock.take()
        } else {
            None
        };

        if let Some(bytes) = bytes {
            self.load_rom_from_bytes(bytes);
        }

        self.draw_menu_bar(ui);
        self.draw_cpu_panel(ui);
        self.draw_main_panel(ui);

        if self.running {
            if let Some(state) = self.state.as_mut() {
                state.step_frame();
            }
            ui.request_repaint();
        }
    }
}

impl NessyApp {
    fn load_rom_from_bytes(&mut self, bytes: Vec<u8>) {
        self.error = None;

        // TODO: Implement proper error handling for cartridge loading. For now, we catch any panics that may occur during the loading process.

        let res = Cartridge::from_raw(&bytes);

        match res {
            Ok(cartridge) => {
                self.state = Some(EmulatorState::new(cartridge));
                self.running = true;
            }
            Err(e) => {
                self.error = Some(format!("Failed to load ROM from bytes: {}", e));
            }
        }
    }

    fn draw_menu_bar(&mut self, ui: &mut eframe::egui::Ui) {
        egui::Panel::top("menu_bar").show_inside(ui, |ui| {
            ui.horizontal(|ui| {
                if ui.button("Load ROM").clicked() {
                    let rx = self.rom_bytes_rx.clone();

                    #[cfg(not(target_arch = "wasm32"))]
                    {
                        if let Some(path) = rfd::FileDialog::new()
                            .add_filter("NES ROM", &["nes"])
                            .pick_file()
                        {
                            if let Ok(bytes) = std::fs::read(&path) {
                                *rx.lock().unwrap() = Some(bytes);
                            }
                        }
                    }

                    #[cfg(target_arch = "wasm32")]
                    {
                        wasm_bindgen_futures::spawn_local(async move {
                            let file = rfd::AsyncFileDialog::new()
                                .add_filter("NES ROM", &["nes"])
                                .pick_file()
                                .await;

                            if let Some(file) = file {
                                let bytes = file.read().await;
                                *rx.lock().unwrap() = Some(bytes);
                            }
                        })
                    }
                }

                ui.separator();

                let has_state = self.state.is_some();

                let run_label = if self.running { "Pause" } else { "Run" };

                if ui
                    .add_enabled(has_state, egui::Button::new(run_label))
                    .clicked()
                {
                    self.running = !self.running;
                }

                if ui
                    .add_enabled(has_state && !self.running, egui::Button::new("Step"))
                    .clicked()
                {
                    if let Some(s) = self.state.as_mut() {
                        s.step();
                    }
                }

                if ui
                    .add_enabled(has_state, egui::Button::new("Reset"))
                    .clicked()
                {
                    self.running = false;
                    if let Some(s) = self.state.as_mut() {
                        s.reset();
                    }
                }

                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                    if self.running {
                        ui.label(RichText::new("Running").color(egui::Color32::GREEN));
                    } else if has_state {
                        ui.label(RichText::new("Paused").color(egui::Color32::YELLOW));
                    } else {
                        ui.label(RichText::new("No ROM Loaded").color(egui::Color32::RED));
                    }
                });
            });
        });
    }

    fn draw_cpu_panel(&mut self, ui: &mut eframe::egui::Ui) {
        egui::Panel::right("cpu_panel")
            .resizable(false)
            .min_size(200.0)
            .show_inside(ui, |ui| {
                ui.heading("CPU - 6502");
                ui.separator();

                match &self.state {
                    Some(state) => {
                        let regs = state.registers();
                        draw_registers(ui, &regs);
                        ui.separator();
                        draw_flags(ui, regs.status);
                        ui.separator();
                        ui.label(
                            RichText::new(format!("Cycles: {}", regs.cycles))
                                .color(egui::Color32::from_gray(180)),
                        );
                    }
                    None => {
                        ui.label(RichText::new("No ROM Loaded").color(egui::Color32::GRAY));
                    }
                }
            });
    }

    fn draw_main_panel(&mut self, ui: &mut eframe::egui::Ui) {
        egui::CentralPanel::default().show_inside(ui, |ui| {
            if let Some(err) = &self.error {
                ui.colored_label(Color32::RED, err);
                ui.separator();
            }

            if self.state.is_none() && self.error.is_none() {
                ui.centered_and_justified(|ui| {
                    ui.label(
                        RichText::new("Carga una ROM para empezar")
                            .size(20.0)
                            .color(Color32::GRAY),
                    );
                });
            } else {
                // Placeholder 256×240 (resolución del PPU de la NES)
                // TODO: Reemplazar con textura real renderizada por el PPU.
                let nes_size = egui::vec2(256.0, 240.0);
                let (response, painter) = ui.allocate_painter(nes_size, egui::Sense::hover());
                painter.rect_filled(response.rect, 4.0, Color32::from_rgb(10, 10, 30));
                painter.text(
                    response.rect.center(),
                    egui::Align2::CENTER_CENTER,
                    "PPU — placeholder",
                    egui::FontId::monospace(12.0),
                    Color32::from_gray(80),
                );
            }
        });
    }
}

fn draw_registers(ui: &mut eframe::egui::Ui, regs: &CpuRegisters) {
    egui::Grid::new("cpu_regs")
        .num_columns(2)
        .spacing([16.0, 4.0])
        .show(ui, |ui| {
            reg_row(ui, "PC", format!("{:#06X}", regs.pc));
            reg_row(ui, "SP", format!("{:#04X}  ", regs.sp));
            reg_row(ui, "A ", format!("{:#04X}  ", regs.acc));
            reg_row(ui, "X ", format!("{:#04X}  ", regs.x));
            reg_row(ui, "Y ", format!("{:#04X}  ", regs.y));
            reg_row(ui, "P ", format!("{:#04X}  ", regs.status));
        });
}

fn reg_row(ui: &mut eframe::egui::Ui, label: &str, value: String) {
    ui.label(
        RichText::new(label)
            .color(egui::Color32::from_gray(150))
            .monospace(),
    );
    ui.monospace(RichText::new(value).color(egui::Color32::WHITE));
    ui.end_row();
}

fn draw_flags(ui: &mut eframe::egui::Ui, status: u8) {
    ui.label(
        RichText::new("Flags  N V B D I Z C")
            .color(egui::Color32::from_gray(150))
            .monospace(),
    );
    ui.horizontal(|ui| {
        // Orden: N V _ B D I Z C  (bit 7 al bit 0, saltando el bit 5 unused)
        for (name, mask) in [
            ("N", 0b1000_0000u8),
            ("V", 0b0100_0000),
            ("B", 0b0001_0000),
            ("D", 0b0000_1000),
            ("I", 0b0000_0100),
            ("Z", 0b0000_0010),
            ("C", 0b0000_0001),
        ] {
            let set = status & mask != 0;
            let color = if set {
                Color32::from_rgb(80, 210, 110)
            } else {
                Color32::from_gray(55)
            };
            ui.label(RichText::new(name).color(color).monospace());
        }
    });
}
