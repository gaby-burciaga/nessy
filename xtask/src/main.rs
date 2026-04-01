use std::process::Command;

fn main() {
    run("cargo build --release");
    run("cargo build --release --target x86_64-pc-windows-gnu");
    run("cargo build --release --target wasm32-unknown-unknown");
}

fn run(cmd: &str) {
    let status = Command::new("sh").arg("-c").arg(cmd).status().unwrap();

    if !status.success() {
        panic!("Command failed: {}", cmd);
    }
}
