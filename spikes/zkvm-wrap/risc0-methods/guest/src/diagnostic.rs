#![no_main]

use risc0_zkvm::guest::env;
use ssgkr_zkvm_wrap_spike_common::{
    APPLICATION_STATEMENT_BYTES, Case, DIAGNOSTIC_RELATION_CHECKPOINTS, evaluate_diagnostic,
};

risc0_zkvm::guest::entry!(main);

const DIAGNOSTIC_MAGIC: &[u8; 8] = b"SSGKRCD1";
const CYCLE_TICKS: usize = 2 + DIAGNOSTIC_RELATION_CHECKPOINTS + 1;
const DIAGNOSTIC_BYTES: usize = DIAGNOSTIC_MAGIC.len() + CYCLE_TICKS * 8;

fn main() {
    let mut ticks = [0u64; CYCLE_TICKS];
    ticks[0] = env::cycle_count();

    let selector: u8 = env::read();
    let Some(case) = Case::from_u8(selector) else {
        return;
    };
    ticks[1] = env::cycle_count();

    let Some(statement) = evaluate_diagnostic(case, |stage| {
        ticks[2 + stage as usize] = env::cycle_count();
    }) else {
        return;
    };

    // Preserve the canonical raw192 as the diagnostic journal prefix.
    env::commit_slice(&statement);
    ticks[CYCLE_TICKS - 1] = env::cycle_count();

    let mut diagnostics = [0u8; DIAGNOSTIC_BYTES];
    diagnostics[..DIAGNOSTIC_MAGIC.len()].copy_from_slice(DIAGNOSTIC_MAGIC);
    for (index, tick) in ticks.iter().enumerate() {
        let offset = DIAGNOSTIC_MAGIC.len() + index * 8;
        diagnostics[offset..offset + 8].copy_from_slice(&tick.to_le_bytes());
    }
    env::commit_slice(&diagnostics);

    // Keep the diagnostic prefix contract explicit at compile time.
    let _: [u8; APPLICATION_STATEMENT_BYTES] = statement;
}
