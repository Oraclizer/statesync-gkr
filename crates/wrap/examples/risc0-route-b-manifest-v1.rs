//! Verify and print the checked-in native RISC Zero Route B manifest vector.

use std::env;
use std::fs;
use std::io;

use ssgkr_wrap::risc0_route_b_manifest::Risc0RouteBManifestVectorV1;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args().skip(1);
    let path = args
        .next()
        .ok_or_else(|| io::Error::other("usage: risc0-route-b-manifest-v1 PATH-TO-VECTOR"))?;
    if args.next().is_some() {
        return Err(io::Error::other("unexpected extra argument").into());
    }
    let json = fs::read_to_string(path)?;
    let vector = Risc0RouteBManifestVectorV1::from_json(&json)?;
    print!("{}", vector.transcript()?);
    Ok(())
}
