pub fn start() {
    #[cfg(target_family = "wasm")]
    start_web();

    #[cfg(not(target_family = "wasm"))]
    start_native();
}

#[cfg(not(target_family = "wasm"))]
fn start_native() {
    let options = eframe::NativeOptions::default();

    eframe::run_native("Nessy", options, Box::new(|_cc| Ok(Box::new(NessyApp {})))).unwrap();
}

#[cfg(target_family = "wasm")]
fn start_web() {
    use eframe::wasm_bindgen::JsCast as _;

    let web_options = eframe::WebOptions::default();

    wasm_bindgen_futures::spawn_local(async {
        let doc = web_sys::window()
            .expect("No window")
            .document()
            .expect("No document");
        let canvas = doc
            .get_element_by_id("the_canvas_id")
            .expect("No canvas")
            .dyn_into::<web_sys::HtmlCanvasElement>()
            .expect("the_canvas_id was not a HtmlCanvasElement");

        let start_result = eframe::WebRunner::new()
            .start(
                canvas,
                web_options,
                Box::new(|_cc| Ok(Box::new(NessyApp {}))),
            )
            .await;

        if let Some(loading_text) = doc.get_element_by_id("loading_text") {
            match start_result {
                Ok(_) => {
                    loading_text.remove();
                }
                Err(e) => {
                    loading_text.set_inner_html(
                        "<p> The app has crashed. See the developer console for details. </p>",
                    );
                    panic!("Failed to start eframe: {e:?}");
                }
            }
        }
    });
}

struct NessyApp {}

impl eframe::App for NessyApp {
    fn ui(&mut self, ui: &mut eframe::egui::Ui, _frame: &mut eframe::Frame) {
        ui.label("Hello nessy");
    }
}
