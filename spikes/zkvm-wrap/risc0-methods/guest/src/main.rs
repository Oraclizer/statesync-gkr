#![no_main]

use risc0_zkvm::guest::env;
use ssgkr_zkvm_wrap_spike_common::{
    evaluate_with_pinned_material, read_pinned_artifact_input,
};

risc0_zkvm::guest::entry!(main);

fn main() {
    let Some((selector, material)) = read_pinned_artifact_input(env::stdin()) else {
        return;
    };
    if let Some(statement) = evaluate_with_pinned_material(selector, material) {
        // The journal contract is the exact unframed 192-byte WrapStatementV1.
        env::commit_slice(&statement);
    }
}
