//! Reference proof server and load frontend built from the serving
//! components. Commands: `server`, `load`, `controls`, `sweep-plan`, `help`.
//! See the crate README for options and the serving modes.

mod cli;
mod load;
mod server;
mod shared;

use shared::{Logger, Result, State, fresh_json, out_dir, provenance, u64_arg, usize_arg};

fn run() -> Result<()> {
    let command = std::env::args().nth(1).unwrap_or_else(|| "help".into());
    cli::validate(&command)?;
    match command.as_str() {
        "server" => server::run(),
        "load" => load::run(),
        "controls" => {
            let out = out_dir()?;
            let log = Logger::new(&out.join("controls.jsonl"), 1)?;
            fresh_json(&out.join("metadata.json"), &provenance("controls"))?;
            let depth =
                u32::try_from(u64_arg("--depth", "24")?).map_err(|_| "depth overflows u32")?;
            let state = State::new(depth, usize_arg("--workers", "4")?, &log)?;
            state.controls(usize_arg("--control-samples", "4")?, &out, &log)?;
            fresh_json(
                &out.join("terminal.json"),
                &serde_json::json!({"status": "CONTROLS_PASS", "logging": log.finish()?}),
            )?;
            Ok(())
        }
        "sweep-plan" => load::sweep_plan(),
        _ => {
            eprintln!(
                "ssgkr-serving server|load|controls|sweep-plan --out NEW_DIR [options]; see README.md"
            );
            if command == "help" {
                Ok(())
            } else {
                Err(format!("unknown command: {command}").into())
            }
        }
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("serving failed: {e}");
        std::process::exit(1);
    }
}
