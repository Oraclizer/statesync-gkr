//! Pre-execution CLI shape guard. All current options take one explicit value.
//! Keep this list in parity with the calling command and shared argument reads.
use crate::shared::Result;
use std::collections::HashSet;

const CONTROLS:&[&str]=&[
    "--out","--host-id","--run-id","--repeat",
    "--workers","--depth","--control-samples",
];
const SERVER:&[&str]=&[
    "--out","--host-id","--run-id","--repeat",
    "--listen","--workers","--batch-max","--max-wait-us","--max-queue",
    "--run-ms","--io-timeout-ms","--log-flush-every","--depth",
    "--control-samples","--telemetry-ms",
];
const LOAD:&[&str]=&[
    "--out","--host-id","--run-id","--repeat",
    "--depth","--verify-workers","--corpus","--control-samples","--mixture",
    "--targets","--rate","--duration-sec","--jobs","--warmup-jobs",
    "--deadline-ms","--sender-queue","--max-pending","--log-flush-every",
    "--telemetry-ms","--verify-queue","--io-timeout-ms","--deadline-poll-ms",
    "--drain-ms",
];
const SWEEP:&[&str]=&[
    "--out","--workers-list","--batch-list","--rate-list","--wait-us-list",
    "--repeats","--mixture","--targets","--sweep-phase",
];

pub fn validate(command:&str)->Result<()> {
    let allowed=match command {
        "controls"=>CONTROLS,"server"=>SERVER,"load"=>LOAD,"sweep-plan"=>SWEEP,
        "help"=>&[],_=>return Err(format!("unknown command: {command}; use server, load, controls, sweep-plan, or help").into()),
    };
    let args:Vec<String>=std::env::args().skip(2).collect();
    let mut seen=HashSet::new(); let mut i=0;
    while i<args.len() {
        let option=args[i].as_str();
        if !allowed.contains(&option) {
            if option=="--servers" {
                return Err("unsupported option --servers; use load --targets HOST:PORT[,HOST:PORT]. Aliases are not accepted.".into());
            }
            return Err(format!("unsupported option or positional argument {option} for {command}; options must use --name VALUE syntax").into());
        }
        if !seen.insert(option) { return Err(format!("duplicate option {option} for {command}").into()); }
        let Some(value)=args.get(i+1) else { return Err(format!("missing value for {option}").into()); };
        if value.is_empty()||value.starts_with("--") { return Err(format!("missing value for {option}; the next option is not a value").into()); }
        i+=2;
    }
    Ok(())
}
