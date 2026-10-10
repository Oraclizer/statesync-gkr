use std::{env, fs, io::Cursor, path::Path};

use anyhow::{bail, ensure, Context, Result};
use risc0_zkvm::{sha::Digest, InnerReceipt, Receipt};
use sha2::{Digest as _, Sha256};
use sha3::Keccak256;

const PROOF_PAYLOAD_BYTES: usize = 279_130;
const PROOF_PAYLOAD_SHA256: [u8; 32] = [
    0x2e, 0xd1, 0x07, 0x36, 0x8d, 0x0e, 0x3c, 0xc2, 0xf2, 0x3b, 0x4c, 0x83, 0x66, 0xac, 0x7f, 0x59,
    0x92, 0x11, 0x5f, 0xa3, 0x7a, 0x2a, 0xbb, 0xd3, 0x39, 0x53, 0xfb, 0xb7, 0x83, 0x30, 0x58, 0x2a,
];
const PROGRAM_BINARY_BYTES: usize = 706_152;
const PROGRAM_BINARY_SHA256: [u8; 32] = [
    0x7d, 0xcb, 0x6d, 0x1d, 0xdd, 0x47, 0x61, 0x8f, 0x65, 0xa2, 0x50, 0x36, 0x1a, 0x4b, 0x9e, 0x3f,
    0xdb, 0x77, 0xbe, 0x11, 0x04, 0xf5, 0x1c, 0x66, 0x22, 0x5b, 0x78, 0xe1, 0x14, 0xc7, 0xa9, 0xba,
];
const IMAGE_ID: [u8; 32] = [
    0xdd, 0x94, 0x7f, 0xec, 0x1f, 0xe2, 0x70, 0xc4, 0x1b, 0xc0, 0x45, 0x79, 0x12, 0xe1, 0xe7, 0x74,
    0x27, 0xc1, 0x67, 0x97, 0xac, 0x47, 0xdc, 0x6a, 0x1c, 0x82, 0x5a, 0x93, 0x23, 0x64, 0x86, 0x43,
];
const RAW192_HEX: &str = concat!(
    "01000100010001001f0000001800000000000000000000000000000000000000",
    "abde249a257cd4e6c3ed34f2749a7d8be66fd418f5a5d8595bffc956b45f0e00",
    "88957f2aa94f0f483d11f6bbc00b37db9fedd7911eee56e15c1661e148453200",
    "88957f2aa94f0f483d11f6bbc00b37db9fedd7911eee56e15c1661e148453200",
    "0500000000000000000000000000000000000000000000000000000000000000",
    "4cc6356134cfb0dcefee384334580a10c3f82929f64a9f8833dd47ebc2cdbf00",
);
const RAW192_SHA256: [u8; 32] = [
    0x95, 0x95, 0x50, 0xf3, 0x84, 0x7e, 0x15, 0xae, 0x2d, 0x69, 0xab, 0x02, 0x7d, 0x8e, 0xf5, 0x96,
    0x21, 0x28, 0x2e, 0xeb, 0x75, 0x87, 0x46, 0x26, 0x22, 0x05, 0xfa, 0x3f, 0x61, 0xb3, 0x87, 0x21,
];
const VERIFIER_VERSION_HASH: [u8; 32] = [
    0xaa, 0x24, 0x36, 0x8f, 0x9c, 0xe9, 0x02, 0x5f, 0x58, 0x59, 0x6d, 0x96, 0x62, 0x09, 0xfc, 0x3f,
    0x32, 0x2c, 0x8c, 0xac, 0x37, 0xda, 0xe7, 0x53, 0xbb, 0x9b, 0x03, 0x67, 0xd2, 0x73, 0x70, 0x0d,
];
const STATEMENT_LEAF: [u8; 32] = [
    0xb4, 0xb0, 0x58, 0xae, 0x36, 0xbc, 0xc8, 0x35, 0x72, 0x41, 0xb0, 0xc3, 0x08, 0x63, 0x0d, 0x7b,
    0xa2, 0x03, 0xbd, 0x47, 0x72, 0x6e, 0xdb, 0xad, 0x5e, 0xd1, 0x6b, 0x04, 0xaf, 0xeb, 0x84, 0x92,
];

fn digest_sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn digest_keccak256(bytes: &[u8]) -> [u8; 32] {
    Keccak256::digest(bytes).into()
}

fn expected_raw192() -> Result<[u8; 192]> {
    let bytes = hex::decode(RAW192_HEX).context("decode frozen raw192")?;
    bytes
        .try_into()
        .map_err(|bytes: Vec<u8>| anyhow::anyhow!("raw192 length mismatch: {}", bytes.len()))
}

fn statement_leaf(raw192: &[u8; 192]) -> [u8; 32] {
    let mut preimage = Vec::with_capacity(128);
    preimage.extend_from_slice(&digest_keccak256(b"risc0"));
    preimage.extend_from_slice(&IMAGE_ID);
    preimage.extend_from_slice(&VERIFIER_VERSION_HASH);
    preimage.extend_from_slice(&digest_keccak256(raw192));
    digest_keccak256(&preimage)
}

fn strict_inner_only_value(payload: &[u8]) -> Result<ciborium::value::Value> {
    use ciborium::value::Value;
    let mut cursor = Cursor::new(payload);
    let decoded: Value = ciborium::from_reader(&mut cursor).context("decode proof CBOR")?;
    ensure!(
        cursor.position() == payload.len() as u64,
        "trailing CBOR bytes"
    );
    let Value::Map(fields) = decoded else {
        bail!("proof payload must be a CBOR map")
    };
    ensure!(
        fields.len() == 1,
        "proof payload must contain exactly one field"
    );
    let (key, inner) = fields.into_iter().next().expect("one field checked");
    ensure!(
        key == Value::Text("inner".to_owned()),
        "field must be named inner"
    );
    let canonical_wire = Value::Map(vec![(Value::Text("inner".to_owned()), inner.clone())]);
    let mut reencoded = Vec::new();
    ciborium::into_writer(&canonical_wire, &mut reencoded).context("re-encode payload")?;
    ensure!(
        reencoded == payload,
        "payload is not an exact inner-only re-encoding"
    );
    Ok(inner)
}

fn decode_inner_only_receipt(payload: &[u8]) -> Result<InnerReceipt> {
    use ciborium::value::Value;
    let inner_value = strict_inner_only_value(payload)?;
    let mut encoded_inner = Vec::new();
    ciborium::into_writer(&inner_value, &mut encoded_inner).context("encode inner value")?;
    let inner: InnerReceipt =
        ciborium::from_reader(encoded_inner.as_slice()).context("decode v3.0.4 InnerReceipt")?;
    let mut typed_inner_cbor = Vec::new();
    ciborium::into_writer(&inner, &mut typed_inner_cbor).context("re-encode typed inner")?;
    let typed_inner_value: Value =
        ciborium::from_reader(typed_inner_cbor.as_slice()).context("decode typed inner value")?;
    let typed_wire = Value::Map(vec![(Value::Text("inner".to_owned()), typed_inner_value)]);
    let mut typed_payload = Vec::new();
    ciborium::into_writer(&typed_wire, &mut typed_payload).context("re-encode typed payload")?;
    ensure!(
        typed_payload == payload,
        "typed InnerReceipt exact re-encode mismatch"
    );
    Ok(inner)
}

fn verify_saved_proof(path: &Path) -> Result<()> {
    let payload = fs::read(path).with_context(|| format!("read proof {}", path.display()))?;
    ensure!(payload.len() == PROOF_PAYLOAD_BYTES, "proof size mismatch");
    ensure!(
        digest_sha256(&payload) == PROOF_PAYLOAD_SHA256,
        "proof hash mismatch"
    );
    let raw192 = expected_raw192()?;
    ensure!(
        digest_sha256(&raw192) == RAW192_SHA256,
        "raw192 hash mismatch"
    );
    ensure!(
        statement_leaf(&raw192) == STATEMENT_LEAF,
        "statement leaf mismatch"
    );
    let inner = decode_inner_only_receipt(&payload)?;
    ensure!(
        inner.succinct().is_ok(),
        "stored InnerReceipt is not succinct"
    );
    let image_id = Digest::from_bytes(IMAGE_ID);
    let receipt = Receipt::new(inner.clone(), raw192.to_vec());
    receipt
        .verify(image_id)
        .context("verify final-identity Receipt")?;
    let mut wrong_raw192 = raw192;
    wrong_raw192[0] ^= 1;
    ensure!(
        Receipt::new(inner.clone(), wrong_raw192.to_vec())
            .verify(image_id)
            .is_err(),
        "wrong raw192 unexpectedly verified"
    );
    let mut wrong_image_id_bytes = IMAGE_ID;
    wrong_image_id_bytes[0] ^= 1;
    ensure!(
        receipt
            .verify(Digest::from_bytes(wrong_image_id_bytes))
            .is_err(),
        "wrong Image ID unexpectedly verified"
    );
    println!(
        "vendor=risc0\nversion=3.0.4\nmode=verify_saved_inner_only_receipt_no_execution_no_proof"
    );
    println!("proof_payload_bytes={PROOF_PAYLOAD_BYTES}");
    println!("proof_payload_sha256={}", hex::encode(PROOF_PAYLOAD_SHA256));
    println!("proof_wire=zkverify_risc0_verifier_proof_inner_only");
    println!("strict_inner_only_cbor=PASS\ntyped_exact_reencode=PASS\nproof_kind=succinct");
    println!("program_binary_bytes={PROGRAM_BINARY_BYTES}");
    println!(
        "program_binary_sha256={}",
        hex::encode(PROGRAM_BINARY_SHA256)
    );
    println!("program_binary_binding_owner=pinned_two_clean_provenance");
    println!("image_id={}", hex::encode(IMAGE_ID));
    println!("raw192={RAW192_HEX}");
    println!("raw192_sha256={}", hex::encode(RAW192_SHA256));
    println!(
        "verifier_version_hash={}",
        hex::encode(VERIFIER_VERSION_HASH)
    );
    println!("statement_leaf={}", hex::encode(STATEMENT_LEAF));
    println!("receipt_local_verify=PASS\nwrong_raw192_negative_verify=PASS\nwrong_image_id_negative_verify=PASS");
    Ok(())
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let path = args
        .next()
        .map(std::path::PathBuf::from)
        .ok_or_else(|| anyhow::anyhow!("expected saved proof CBOR path"))?;
    ensure!(
        args.next().is_none(),
        "unexpected argument after proof path"
    );
    verify_saved_proof(&path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ciborium::value::Value;
    fn encode(value: &Value) -> Vec<u8> {
        let mut bytes = Vec::new();
        ciborium::into_writer(value, &mut bytes).unwrap();
        bytes
    }
    #[test]
    fn frozen_raw192_recomputes_hash_and_statement_leaf() {
        let raw192 = expected_raw192().unwrap();
        assert_eq!(digest_sha256(&raw192), RAW192_SHA256);
        assert_eq!(statement_leaf(&raw192), STATEMENT_LEAF);
    }
    #[test]
    fn inner_only_wire_rejects_shape_and_trailing_mutations() {
        assert!(strict_inner_only_value(&encode(&Value::Map(vec![]))).is_err());
        assert!(strict_inner_only_value(&encode(&Value::Map(vec![(
            Value::Text("proof".into()),
            Value::Null
        )])))
        .is_err());
        assert!(strict_inner_only_value(&encode(&Value::Map(vec![
            (Value::Text("inner".into()), Value::Null),
            (Value::Text("journal".into()), Value::Bytes(vec![]))
        ])))
        .is_err());
        let mut trailing = encode(&Value::Map(vec![(
            Value::Text("inner".into()),
            Value::Null,
        )]));
        trailing.push(0);
        assert!(strict_inner_only_value(&trailing).is_err());
    }
}
