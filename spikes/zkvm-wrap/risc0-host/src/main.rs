use std::{
    env,
    fs::File,
    io::{Cursor, Read},
    path::{Path, PathBuf},
    time::Instant,
};

#[cfg(feature = "prove")]
use std::fs;

use anyhow::{bail, ensure, Context, Result};
use risc0_zkvm::{default_executor, ExecutorEnv};
#[cfg(feature = "prove")]
use risc0_zkvm::{default_prover, ProverOpts};
use sha2::Sha256;
use sha3::{Digest, Keccak256};
use ssgkr_risc0_wrap_spike_methods::{
    SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST_ELF, SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST_ID,
    SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF, SSGKR_RISC0_WRAP_SPIKE_GUEST_ID,
};
use ssgkr_zkvm_wrap_spike_common::{
    APPLICATION_STATEMENT_BYTES, ARTIFACT_INPUT_HEADER_BYTES, Case,
    PINNED_PREPARED_MATERIAL_BYTES, PINNED_PREPARED_MATERIAL_LENGTH_LE, evaluate,
};

const DIAGNOSTIC_MAGIC: &[u8; 8] = b"SSGKRCD1";
const PREPARED_MATERIAL_PATH_ENV: &str = "SSGKR_PREPARED_MATERIAL_PATH";
const DIAGNOSTIC_TICK_NAMES: [&str; 8] = [
    "guest_entry",
    "input_decoded",
    "prover_constructed",
    "relation_prepared",
    "fixture_and_frozen_proof_copied",
    "wrap_relation_complete",
    "raw192_encoded",
    "raw192_committed",
];

const RISC0_VERSION_HASH_V3_0: [u8; 32] = [
    0xaa, 0x24, 0x36, 0x8f, 0x9c, 0xe9, 0x02, 0x5f, 0x58, 0x59, 0x6d, 0x96, 0x62, 0x09, 0xfc, 0x3f,
    0x32, 0x2c, 0x8c, 0xac, 0x37, 0xda, 0xe7, 0x53, 0xbb, 0x9b, 0x03, 0x67, 0xd2, 0x73, 0x70, 0x0d,
];

fn image_id_words_to_vk_be_bytes(words: &[u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, word) in words.iter().enumerate() {
        // risc0-build emits Digest::as_words(), whose values represent the
        // canonical big-endian digest bytes in native u32 storage. Normalize
        // that representation explicitly, then emit the zkVerify H256 bytes.
        let canonical_word = u32::from_be(*word);
        bytes[index * 4..(index + 1) * 4].copy_from_slice(&canonical_word.to_be_bytes());
    }
    bytes
}

fn image_id_vk_be_bytes() -> [u8; 32] {
    image_id_words_to_vk_be_bytes(&SSGKR_RISC0_WRAP_SPIKE_GUEST_ID)
}

fn diagnostic_image_id_vk_be_bytes() -> [u8; 32] {
    image_id_words_to_vk_be_bytes(&SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST_ID)
}

fn keccak256(bytes: &[u8]) -> [u8; 32] {
    Keccak256::digest(bytes).into()
}

fn statement_leaf(raw192: &[u8]) -> [u8; 32] {
    let mut statement_preimage = [0u8; 128];
    statement_preimage[..32].copy_from_slice(&keccak256(b"risc0"));
    statement_preimage[32..64].copy_from_slice(&image_id_vk_be_bytes());
    statement_preimage[64..96].copy_from_slice(&RISC0_VERSION_HASH_V3_0);
    statement_preimage[96..].copy_from_slice(&keccak256(raw192));
    keccak256(&statement_preimage)
}

fn prepared_material_path() -> Result<PathBuf> {
    env::var_os(PREPARED_MATERIAL_PATH_ENV)
        .map(PathBuf::from)
        .context("SSGKR_PREPARED_MATERIAL_PATH must name the approved artifact")
}

fn canonical_guest_env(path: &Path, selector: u8) -> Result<risc0_zkvm::ExecutorEnv<'static>> {
    let material =
        File::open(path).with_context(|| format!("open prepared material {}", path.display()))?;
    let metadata = material
        .metadata()
        .with_context(|| format!("stat opened prepared material {}", path.display()))?;
    ensure!(
        metadata.is_file(),
        "prepared material path must name a regular file"
    );
    ensure!(
        metadata.len() == PINNED_PREPARED_MATERIAL_BYTES as u64,
        "prepared material length mismatch: expected {}, got {}",
        PINNED_PREPARED_MATERIAL_BYTES,
        metadata.len()
    );

    let mut header = [0u8; ARTIFACT_INPUT_HEADER_BYTES];
    header[0] = selector;
    header[1..].copy_from_slice(&PINNED_PREPARED_MATERIAL_LENGTH_LE);
    let input = Cursor::new(header).chain(material);

    let mut builder = ExecutorEnv::builder();
    builder.stdin(input);
    builder.build().context("build canonical raw-input guest env")
}

fn execute_honest(repeats: usize) -> Result<()> {
    ensure!(repeats > 0, "repeat count must be positive");
    let material_path = prepared_material_path()?;
    let expected = evaluate(Case::Honest).context("native honest relation must accept")?;
    let executor = default_executor();
    let started = Instant::now();
    let mut cycles = Vec::with_capacity(repeats);
    let mut segments = Vec::with_capacity(repeats);
    let mut run_ms = Vec::with_capacity(repeats);

    for index in 0..repeats {
        let run_started = Instant::now();
        let guest_env = canonical_guest_env(&material_path, Case::Honest as u8)?;
        let session = executor.execute(guest_env, SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF)?;
        ensure!(
            session.journal.bytes == expected,
            "guest/native raw192 mismatch at run {index}"
        );
        cycles.push(session.cycles());
        segments.push(session.segments.len());
        run_ms.push(run_started.elapsed().as_millis());
    }

    println!("vendor=risc0");
    println!("version=3.0.4");
    println!("mode=execute_only_no_proof");
    println!("runs={repeats}");
    println!("prepared_material_path={}", material_path.display());
    println!("prepared_material_bytes={PINNED_PREPARED_MATERIAL_BYTES}");
    println!("elf_bytes={}", SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF.len());
    println!(
        "elf_sha256={}",
        hex::encode(Sha256::digest(SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF))
    );
    println!("image_id_vk_be={}", hex::encode(image_id_vk_be_bytes()));
    println!("application_statement_bytes={}", expected.len());
    println!("raw192_sha256={}", hex::encode(Sha256::digest(expected)));
    println!("statement_leaf={}", hex::encode(statement_leaf(&expected)));
    println!("cycles={cycles:?}");
    println!("segments={segments:?}");
    println!("run_ms={run_ms:?}");
    println!("elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}

fn execute_battery() -> Result<()> {
    let material_path = prepared_material_path()?;
    let executor = default_executor();
    let started = Instant::now();
    for selector in 1u8..=6 {
        let guest_env = canonical_guest_env(&material_path, selector)?;
        let session = executor.execute(guest_env, SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF)?;
        ensure!(
            session.journal.bytes.is_empty(),
            "selector {selector} unexpectedly committed public bytes"
        );
        println!(
            "selector={selector} result=rejected journal_bytes=0 cycles={} segments={}",
            session.cycles(),
            session.segments.len()
        );
    }
    println!("battery_elapsed_ms={}", started.elapsed().as_millis());
    Ok(())
}

fn execute_diagnostic() -> Result<()> {
    let expected = evaluate(Case::Honest).context("native honest relation must accept")?;
    let guest_env = ExecutorEnv::builder()
        .write(&(Case::Honest as u8))?
        .build()?;
    let started = Instant::now();
    let session =
        default_executor().execute(guest_env, SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST_ELF)?;
    let elapsed_ms = started.elapsed().as_millis();

    let diagnostics_offset = APPLICATION_STATEMENT_BYTES;
    let expected_journal_bytes = diagnostics_offset + DIAGNOSTIC_MAGIC.len() + 8 * 8;
    ensure!(
        session.journal.bytes.len() == expected_journal_bytes,
        "unexpected diagnostic journal length"
    );
    ensure!(
        session.journal.bytes[..diagnostics_offset] == expected,
        "diagnostic raw192 prefix differs from canonical output"
    );
    ensure!(
        &session.journal.bytes[diagnostics_offset..diagnostics_offset + DIAGNOSTIC_MAGIC.len()]
            == DIAGNOSTIC_MAGIC,
        "diagnostic journal magic mismatch"
    );

    let mut ticks = [0u64; 8];
    let ticks_offset = diagnostics_offset + DIAGNOSTIC_MAGIC.len();
    for (index, tick) in ticks.iter_mut().enumerate() {
        let offset = ticks_offset + index * 8;
        *tick = u64::from_le_bytes(session.journal.bytes[offset..offset + 8].try_into()?);
    }
    ensure!(
        ticks.windows(2).all(|pair| pair[0] <= pair[1]),
        "diagnostic cycle ticks must be monotonic"
    );

    println!("vendor=risc0");
    println!("version=3.0.4");
    println!("mode=execute_only_diagnostic_no_proof");
    println!("runs=1");
    println!("cycle_counter_trust=host_provided_not_circuit_checked");
    println!("diagnostic_guest_distinct=true");
    println!(
        "canonical_elf_sha256={}",
        hex::encode(Sha256::digest(SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF))
    );
    println!(
        "canonical_image_id_vk_be={}",
        hex::encode(image_id_vk_be_bytes())
    );
    println!(
        "diagnostic_elf_sha256={}",
        hex::encode(Sha256::digest(SSGKR_RISC0_WRAP_SPIKE_DIAGNOSTIC_GUEST_ELF))
    );
    println!(
        "diagnostic_image_id_vk_be={}",
        hex::encode(diagnostic_image_id_vk_be_bytes())
    );
    println!("canonical_raw192_equals_diagnostic=true");
    println!("raw192_sha256={}", hex::encode(Sha256::digest(expected)));
    println!("session_cycles={}", session.cycles());
    println!("segments={}", session.segments.len());
    println!("elapsed_ms={elapsed_ms}");
    for index in 1..ticks.len() {
        println!(
            "stage={} start_cycle={} end_cycle={} cycles={}",
            DIAGNOSTIC_TICK_NAMES[index],
            ticks[index - 1],
            ticks[index],
            ticks[index] - ticks[index - 1]
        );
    }
    println!(
        "post_raw192_commit_cycles={}",
        session.cycles().saturating_sub(ticks[ticks.len() - 1])
    );
    Ok(())
}

#[cfg(feature = "prove")]
fn zkverify_v3_proof_payload(receipt: &risc0_zkvm::Receipt) -> Result<Vec<u8>> {
    use ciborium::value::Value;

    // zkVerify's exact parser target is risc0_verifier::Proof { inner }.
    // Serialize only that one-field structure; the journal and metadata from
    // risc0_zkvm::Receipt are separate wire fields and must not be duplicated.
    let mut inner_cbor = Vec::new();
    ciborium::into_writer(&receipt.inner, &mut inner_cbor)
        .context("serialize InnerReceipt as CBOR value")?;
    let inner: Value =
        ciborium::from_reader(inner_cbor.as_slice()).context("decode InnerReceipt CBOR value")?;
    let wire = Value::Map(vec![(Value::Text("inner".to_owned()), inner)]);

    let mut proof = Vec::new();
    ciborium::into_writer(&wire, &mut proof)
        .context("serialize zkVerify risc0_verifier::Proof wire as CBOR")?;
    ensure!(
        proof.len() <= 1_400_000,
        "CBOR proof payload exceeds Volta Risc0MaxProofSize"
    );

    let roundtrip: Value =
        ciborium::from_reader(proof.as_slice()).context("decode zkVerify proof payload CBOR")?;
    ensure!(
        roundtrip == wire,
        "zkVerify proof payload CBOR roundtrip mismatch"
    );
    let Value::Map(fields) = &roundtrip else {
        bail!("zkVerify proof payload must be a CBOR map")
    };
    ensure!(
        fields.len() == 1 && fields[0].0 == Value::Text("inner".to_owned()),
        "zkVerify proof payload must contain only the inner field"
    );
    Ok(proof)
}

#[cfg(feature = "prove")]
fn prove_succinct(path: PathBuf) -> Result<()> {
    ensure!(
        env::var_os("RISC0_DEV_MODE").is_none(),
        "RISC0_DEV_MODE must be unset; this binary also compiles disable-dev-mode"
    );
    let material_path = prepared_material_path()?;
    let expected = evaluate(Case::Honest).context("native honest relation must accept")?;
    let guest_env = canonical_guest_env(&material_path, Case::Honest as u8)?;
    let opts = ProverOpts::succinct();
    ensure!(!opts.dev_mode(), "dev mode must be disabled");

    let prove_started = Instant::now();
    let prove_info =
        default_prover().prove_with_opts(guest_env, SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF, &opts)?;
    let prove_ms = prove_started.elapsed().as_millis();
    let receipt = prove_info.receipt;
    ensure!(receipt.inner.succinct().is_ok(), "receipt must be succinct");
    ensure!(
        receipt.journal.bytes == expected,
        "receipt journal must equal raw192"
    );

    let verify_started = Instant::now();
    receipt.verify(SSGKR_RISC0_WRAP_SPIKE_GUEST_ID)?;
    let local_verify_ms = verify_started.elapsed().as_millis();

    let proof_payload = zkverify_v3_proof_payload(&receipt)?;

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
    }
    fs::write(&path, &proof_payload).with_context(|| format!("write {}", path.display()))?;

    println!("vendor=risc0");
    println!("version=3.0.4");
    println!("mode=secure_succinct_proof_disable_dev_mode");
    println!("proof_kind=succinct");
    println!("prove_ms={prove_ms}");
    println!("local_verify_ms={local_verify_ms}");
    println!("segments={}", prove_info.stats.segments);
    println!("total_cycles={}", prove_info.stats.total_cycles);
    println!("user_cycles={}", prove_info.stats.user_cycles);
    println!("paging_cycles={}", prove_info.stats.paging_cycles);
    println!("reserved_cycles={}", prove_info.stats.reserved_cycles);
    println!("journal_bytes={}", expected.len());
    println!("raw192_sha256={}", hex::encode(Sha256::digest(expected)));
    println!("elf_bytes={}", SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF.len());
    println!(
        "elf_sha256={}",
        hex::encode(Sha256::digest(SSGKR_RISC0_WRAP_SPIKE_GUEST_ELF))
    );
    println!("image_id_vk_be={}", hex::encode(image_id_vk_be_bytes()));
    println!(
        "verifier_version_hash={}",
        hex::encode(RISC0_VERSION_HASH_V3_0)
    );
    println!("statement_leaf={}", hex::encode(statement_leaf(&expected)));
    println!("proof_wire=zkverify_risc0_verifier_proof_inner_only");
    println!("proof_payload_cbor_path={}", path.display());
    println!("proof_payload_cbor_bytes={}", proof_payload.len());
    println!(
        "proof_payload_cbor_sha256={}",
        hex::encode(Sha256::digest(&proof_payload))
    );
    Ok(())
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    match args.next().as_deref().unwrap_or("execute") {
        "execute" => {
            let repeats = args
                .next()
                .map(|value| value.parse::<usize>().context("parse repeat count"))
                .transpose()?
                .unwrap_or(1);
            execute_honest(repeats)
        }
        "battery" => execute_battery(),
        "diagnostic" => execute_diagnostic(),
        #[cfg(feature = "prove")]
        "prove" => {
            let path = args
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("artifacts/risc0-v3.0.4-zkverify-proof.cbor"));
            prove_succinct(path)
        }
        #[cfg(not(feature = "prove"))]
        "prove" => bail!("prove mode requires the optional `prove` feature"),
        other => bail!("unknown mode {other:?}; expected execute, battery, diagnostic, or prove"),
    }
}

#[cfg(test)]
mod tests {
    use std::io::{self, Cursor, Read};

    use super::{image_id_words_to_vk_be_bytes, statement_leaf};
    use ssgkr_zkvm_wrap_spike_common::{
        ARTIFACT_INPUT_HEADER_BYTES, Case, PINNED_PREPARED_MATERIAL_BYTES,
        evaluate_with_pinned_material, read_pinned_artifact_input,
    };

    fn header(selector: u8, length: u32) -> [u8; ARTIFACT_INPUT_HEADER_BYTES] {
        let mut header = [0u8; ARTIFACT_INPUT_HEADER_BYTES];
        header[0] = selector;
        header[1..].copy_from_slice(&length.to_le_bytes());
        header
    }

    fn framed_zeros(selector: u8, payload_bytes: u64) -> impl Read {
        Cursor::new(header(
            selector,
            PINNED_PREPARED_MATERIAL_BYTES as u32,
        ))
        .chain(io::repeat(0).take(payload_bytes))
    }

    struct PanicAfterHeader {
        header: Cursor<[u8; ARTIFACT_INPUT_HEADER_BYTES]>,
    }

    impl Read for PanicAfterHeader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.header.position() < ARTIFACT_INPUT_HEADER_BYTES as u64 {
                self.header.read(buf)
            } else {
                panic!("bad declared length must reject before payload I/O")
            }
        }
    }

    #[test]
    fn image_id_wire_matches_the_official_v3_big_endian_vk_vector() {
        let vector_words = [
            0x2f3b_427f,
            0x9f35_9510,
            0x535c_30e3,
            0xccf5_e928,
            0xc901_ba3e,
            0xfb9b_55f9,
            0x9da5_a3f6,
            0xae77_cc73,
        ];
        assert_eq!(
            hex::encode(image_id_words_to_vk_be_bytes(&vector_words)),
            "7f423b2f1095359fe3305c5328e9f5cc3eba01c9f9559bfbf6a3a59d73cc77ae"
        );
    }

    #[test]
    fn statement_leaf_is_deterministic_and_length_sensitive() {
        assert_eq!(statement_leaf(&[7u8; 192]), statement_leaf(&[7u8; 192]));
        assert_ne!(statement_leaf(&[7u8; 192]), statement_leaf(&[7u8; 191]));
    }

    #[test]
    fn production_parser_rejects_missing_and_truncated_headers() {
        assert!(read_pinned_artifact_input(Cursor::new(Vec::<u8>::new())).is_none());
        let exact = header(Case::Honest as u8, PINNED_PREPARED_MATERIAL_BYTES as u32);
        for length in 1..ARTIFACT_INPUT_HEADER_BYTES {
            assert!(read_pinned_artifact_input(Cursor::new(exact[..length].to_vec())).is_none());
        }
    }

    #[test]
    fn bad_declared_lengths_reject_before_any_payload_read() {
        for length in [
            0,
            PINNED_PREPARED_MATERIAL_BYTES as u32 - 1,
            PINNED_PREPARED_MATERIAL_BYTES as u32 + 1,
            u32::MAX,
        ] {
            let input = PanicAfterHeader {
                header: Cursor::new(header(Case::Honest as u8, length)),
            };
            assert!(read_pinned_artifact_input(input).is_none());
        }
    }

    #[test]
    fn production_parser_enforces_exact_payload_and_eof() {
        assert!(
            read_pinned_artifact_input(Cursor::new(header(
                Case::Honest as u8,
                PINNED_PREPARED_MATERIAL_BYTES as u32
            )))
            .is_none()
        );
        assert!(
            read_pinned_artifact_input(framed_zeros(
                Case::Honest as u8,
                PINNED_PREPARED_MATERIAL_BYTES as u64 - 1
            ))
            .is_none()
        );

        let (selector, material) = read_pinned_artifact_input(framed_zeros(
            Case::Honest as u8,
            PINNED_PREPARED_MATERIAL_BYTES as u64,
        ))
        .expect("exact framing must parse");
        assert_eq!(selector, Case::Honest as u8);
        assert_eq!(material.len(), PINNED_PREPARED_MATERIAL_BYTES);

        assert!(
            read_pinned_artifact_input(framed_zeros(
                Case::Honest as u8,
                PINNED_PREPARED_MATERIAL_BYTES as u64 + 1
            ))
            .is_none()
        );
        assert!(
            read_pinned_artifact_input(framed_zeros(
                Case::Honest as u8,
                (PINNED_PREPARED_MATERIAL_BYTES as u64) * 2
            ))
            .is_none()
        );
    }

    #[test]
    fn non_honest_selectors_are_preserved_by_transport_and_rejected_by_bridge() {
        for selector in [1, 6, 255] {
            let (parsed, material) = read_pinned_artifact_input(framed_zeros(
                selector,
                PINNED_PREPARED_MATERIAL_BYTES as u64,
            ))
            .expect("selector is transport data");
            assert_eq!(parsed, selector);
            assert!(evaluate_with_pinned_material(parsed, material).is_none());
        }
    }

    #[test]
    fn exact_size_noncanonical_material_rejects_at_the_pinned_bridge() {
        let (_, zeros) = read_pinned_artifact_input(framed_zeros(
            Case::Honest as u8,
            PINNED_PREPARED_MATERIAL_BYTES as u64,
        ))
        .expect("exact all-zero transport must parse");
        assert!(evaluate_with_pinned_material(Case::Honest as u8, zeros).is_none());

        let mut bit_invalid = vec![0u8; PINNED_PREPARED_MATERIAL_BYTES];
        bit_invalid[PINNED_PREPARED_MATERIAL_BYTES / 2] = 1;
        assert!(
            evaluate_with_pinned_material(Case::Honest as u8, bit_invalid).is_none()
        );
    }

    #[test]
    #[ignore = "supervisor-only honest N=1 execute gate"]
    fn honest_n1_execute_gate() -> anyhow::Result<()> {
        super::execute_honest(1)
    }
}
