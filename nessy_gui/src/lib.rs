mod app;

use app::NessyApp;

#[cfg(not(target_family = "wasm"))]
pub fn start() {
    let options = eframe::NativeOptions::default();
    eframe::run_native("Nessy", options, Box::new(|_cc| Ok(Box::new(NessyApp {})))).unwrap();
}

#[cfg(target_family = "wasm")]
pub fn start() {
    use eframe::wasm_bindgen::JsCast as _;

    let web_options = eframe::WebOptions::default();

    wasm_bindgen_futures::spawn_local(async move {
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
