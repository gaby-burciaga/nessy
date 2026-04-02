pub struct NessyApp {}

impl eframe::App for NessyApp {
    fn ui(&mut self, ui: &mut eframe::egui::Ui, _frame: &mut eframe::Frame) {
        ui.label("Hello nessy");
    }
}
