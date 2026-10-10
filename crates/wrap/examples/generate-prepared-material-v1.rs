//! Deterministic host-native generator for the exact A0 PreparedMaterialV1
//! profile. This binary does not build or execute a zkVM guest.

use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use ssgkr_wrap::prepared::{
    GeneratorProvenanceV1, canonical_prepared_material_v1, encode_prepared_material_v1, raw_sha256,
};

const SCHEMA_PROFILE: &str = "PreparedMaterialV1/schema=1/protocol=1/circuit=1/leaf=1/field=koalabear-u32/hash=poseidon2-koalabear-16/pcs=gkr-sparse-mle-v1/config=d24-membership-strategy-a";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (output_path, provenance_path) = parse_args(&raw_args)?;
    let repo = env::current_dir()?;

    let source_commit = command_text(&repo, "git", &["rev-parse", "HEAD"])?;
    let clean_tree = command_bytes(
        &repo,
        "git",
        &["status", "--porcelain=v1", "--untracked-files=no"],
    )?
    .is_empty();
    let rustc_version = command_text(&repo, "rustc", &["-vV"])?;
    let target = rustc_version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .ok_or_else(|| io::Error::other("rustc -vV omitted host target"))?
        .to_owned();

    let material = canonical_prepared_material_v1().map_err(codec_error)?;
    let bytes = encode_prepared_material_v1(&material).map_err(codec_error)?;
    let executable = env::current_exe()?;
    let provenance = GeneratorProvenanceV1 {
        source_commit,
        schema_profile: SCHEMA_PROFILE.to_owned(),
        exact_command: format!("generate-prepared-material-v1 {}", raw_args.join(" ")),
        target,
        generator_binary_sha256: raw_sha256(&fs::read(executable)?),
        input_manifest_sha256: hash_file(&repo.join("Cargo.toml"))?,
        input_lock_sha256: hash_file(&repo.join("Cargo.lock"))?,
        input_toolchain_sha256: hash_file(&repo.join("rust-toolchain.toml"))?,
        output_byte_length: u64::try_from(bytes.len())?,
        output_sha256: raw_sha256(&bytes),
        clean_tree,
    };
    let provenance_text = provenance.to_canonical_text().map_err(codec_error)?;

    fs::write(output_path, bytes)?;
    fs::write(provenance_path, provenance_text.as_bytes())?;
    Ok(())
}

fn parse_args(args: &[String]) -> Result<(PathBuf, PathBuf), io::Error> {
    let mut output = None;
    let mut provenance = None;
    let mut index = 0;
    while index < args.len() {
        let slot = match args[index].as_str() {
            "--output" => &mut output,
            "--provenance" => &mut provenance,
            other => return Err(io::Error::other(format!("unknown argument: {other}"))),
        };
        index += 1;
        let value = args
            .get(index)
            .ok_or_else(|| io::Error::other("missing argument value"))?;
        if slot.replace(PathBuf::from(value)).is_some() {
            return Err(io::Error::other("duplicate output argument"));
        }
        index += 1;
    }
    match (output, provenance) {
        (Some(output), Some(provenance)) => Ok((output, provenance)),
        _ => Err(io::Error::other(
            "usage: generate-prepared-material-v1 --output PATH --provenance PATH",
        )),
    }
}

fn command_text(repo: &Path, program: &str, args: &[&str]) -> Result<String, io::Error> {
    let bytes = command_bytes(repo, program, args)?;
    String::from_utf8(bytes)
        .map(|value| value.trim().to_owned())
        .map_err(io::Error::other)
}

fn command_bytes(repo: &Path, program: &str, args: &[&str]) -> Result<Vec<u8>, io::Error> {
    let output = Command::new(program)
        .args(args)
        .current_dir(repo)
        .output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(io::Error::other(format!(
            "{program} failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        )))
    }
}

fn hash_file(path: &Path) -> Result<[u8; 32], io::Error> {
    Ok(raw_sha256(&fs::read(path)?))
}

fn codec_error(error: impl std::fmt::Debug) -> io::Error {
    io::Error::other(format!("prepared-material codec failed: {error:?}"))
}
