mod fixture;
mod wire;
mod shared;
mod server;
mod load;
mod cli;
use shared::{Result,usize_arg,u64_arg,out_dir,Logger,State,fresh_json,provenance};

fn run()->Result<()> {
    let command=std::env::args().nth(1).unwrap_or_else(||"help".into());
    cli::validate(&command)?;
    match command.as_str() {
        "server"=>server::run(),
        "load"=>load::run(),
        "controls"=> {
            let out=out_dir()?; let log=Logger::new(&out.join("controls.jsonl"),1)?;
            fresh_json(&out.join("metadata.json"),&provenance("controls"))?;
            let state=State::new(u64_arg("--depth","24")? as u32,usize_arg("--workers","4")?,&log)?;
            state.controls(usize_arg("--control-samples","4")?,&out,&log)?;
            fresh_json(&out.join("terminal.json"),&serde_json::json!({"status":"CONTROLS_PASS","logging":log.finish()?}))?; Ok(())
        },
        "sweep-plan"=>load::sweep_plan(),
        _=> { eprintln!("ssgkr-load-driver server|load|controls|sweep-plan --out NEW_DIR [options]; see README.md"); if command=="help" { Ok(()) } else { Err(format!("unknown command: {command}").into()) } }
    }
}
fn main() { if let Err(e)=run() { eprintln!("driver failed: {e}"); std::process::exit(1); } }
