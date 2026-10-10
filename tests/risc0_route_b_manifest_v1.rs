//! Native RISC Zero Route B manifest codec and fail-closed parser battery.

use serde_json::{Map, Value, json};

use statesync_gkr::wrap::risc0_route_b_manifest::{
    RISC0_ROUTE_B_MANIFEST_DOMAIN, Risc0RouteBManifestVectorV1,
};

const VECTOR: &str = include_str!("vectors/risc0-route-b-manifest-v1.json");
const TRANSCRIPT: &str = include_str!("vectors/risc0-route-b-manifest-v1.transcript.txt");
const HISTORICAL_SEALED_FINAL_IDENTITY_CANDIDATE: &str =
    include_str!("vectors/risc0-route-b-final-identity-candidate-v1.json");
const HISTORICAL_SEALED_FINAL_IDENTITY_CANDIDATE_TRANSCRIPT: &str =
    include_str!("vectors/risc0-route-b-final-identity-candidate-v1.transcript.txt");
const VOLTA_2_RUNTIME_REBIND: &str =
    include_str!("vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.json");
const VOLTA_2_RUNTIME_REBIND_TRANSCRIPT: &str =
    include_str!("vectors/risc0-route-b-volta-2.0.0-runtime-rebind-v1.transcript.txt");

fn parse_vector(value: &Value) -> Result<Risc0RouteBManifestVectorV1, String> {
    Risc0RouteBManifestVectorV1::from_json(&value.to_string()).map_err(|error| error.to_string())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(2 + bytes.len() * 2);
    output.push_str("0x");
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

fn object_mut<'a>(
    value: &'a mut Value,
    path: &[&str],
) -> Result<&'a mut Map<String, Value>, String> {
    let mut current = value;
    for component in path {
        current = &mut current[*component];
    }
    current
        .as_object_mut()
        .ok_or_else(|| format!("test fixture path is not an object: {path:?}"))
}

fn value_mut<'a>(value: &'a mut Value, path: &[String]) -> &'a mut Value {
    let mut current = value;
    for component in path {
        current = &mut current[component.as_str()];
    }
    current
}

fn leaf_paths(value: &Value, prefix: &mut Vec<String>, output: &mut Vec<Vec<String>>) {
    match value {
        Value::Object(object) => {
            for (key, child) in object {
                prefix.push(key.clone());
                leaf_paths(child, prefix, output);
                let _ = prefix.pop();
            }
        }
        _ => output.push(prefix.clone()),
    }
}

fn mutate_leaf(value: &mut Value) -> Result<(), String> {
    match value {
        Value::Bool(boolean) => *boolean = !*boolean,
        Value::Number(number) => {
            let next = number
                .as_u64()
                .map_or(0, |current| current.saturating_add(1));
            *value = json!(next);
        }
        Value::String(string) if string.starts_with("0x") => {
            let replacement = if string.ends_with('0') { '1' } else { '0' };
            let _ = string.pop();
            string.push(replacement);
        }
        Value::String(string) => string.push_str("-mutated"),
        _ => return Err("manifest leaves must be scalar JSON values".to_owned()),
    }
    Ok(())
}

#[test]
fn vector_matches_the_sealed_statement_and_route_independent_key_contract() -> Result<(), String> {
    let vector =
        Risc0RouteBManifestVectorV1::from_json(VECTOR).map_err(|error| error.to_string())?;
    let computed = vector.compute().map_err(|error| error.to_string())?;
    assert_eq!(
        hex(&computed.native_statement),
        "0x503151858f2a32b456dc6b8b7a04755c53b177669afa3c287b492c994f6e45ba"
    );
    assert_eq!(
        hex(&computed.raw192_sha256),
        "0x959550f3847e15ae2d69ab027d8ef59621282eeb758746262205fa3f61b38721"
    );
    assert!(!computed.canonical_bytes.is_empty());
    assert_ne!(computed.route_id, [0u8; 32]);
    assert_eq!(
        computed.settlement_key_preimage.len(),
        b"ssgkr/settlement-key/v1".len() + 32 + 8 + 32 + 1
    );
    assert!(
        computed
            .settlement_key_preimage
            .starts_with(b"ssgkr/settlement-key/v1")
    );
    assert_eq!(
        RISC0_ROUTE_B_MANIFEST_DOMAIN,
        b"ssgkr/risc0-route-b-manifest/v1"
    );
    assert_ne!(RISC0_ROUTE_B_MANIFEST_DOMAIN, b"ssgkr/route-manifest/v1");
    assert_eq!(
        vector.transcript().map_err(|error| error.to_string())?,
        TRANSCRIPT
    );
    Ok(())
}

#[test]
fn volta_2_runtime_rebind_recomputes_without_mutating_sealed_vectors() -> Result<(), String> {
    let historical = Risc0RouteBManifestVectorV1::from_json(VECTOR)
        .map_err(|error| error.to_string())?
        .compute()
        .map_err(|error| error.to_string())?;
    let historical_sealed =
        Risc0RouteBManifestVectorV1::from_json(HISTORICAL_SEALED_FINAL_IDENTITY_CANDIDATE)
            .map_err(|error| error.to_string())?;
    let historical_sealed_computed = historical_sealed
        .compute()
        .map_err(|error| error.to_string())?;
    let candidate = Risc0RouteBManifestVectorV1::from_json(VOLTA_2_RUNTIME_REBIND)
        .map_err(|error| error.to_string())?;
    let computed = candidate.compute().map_err(|error| error.to_string())?;

    assert_eq!(
        hex(&historical.route_id),
        "0xed4f72e470c062a3bd86cc60446109363a5f865a1ba373c82ee96d9bbba9d2b8"
    );
    assert_eq!(
        hex(&computed.route_id),
        "0x27b40b99a41976f061e94124b84cc8c43ee4e5ed6bad2e94267057e1d375f2ef"
    );
    assert_eq!(
        hex(&historical_sealed_computed.route_id),
        "0x4ad7339a7667b75298c3a7af9420ebbc6de74d480b1468071ede920964b8c8b0"
    );
    assert_eq!(
        hex(&computed.native_statement),
        "0xb4b058ae36bcc8357241b0c308630d7ba203bd47726edbad5ed16b04afeb8492"
    );
    assert_ne!(computed.route_id, historical.route_id);
    assert_ne!(computed.route_id, historical_sealed_computed.route_id);
    assert_eq!(
        historical_sealed
            .transcript()
            .map_err(|error| error.to_string())?,
        HISTORICAL_SEALED_FINAL_IDENTITY_CANDIDATE_TRANSCRIPT
    );
    assert_eq!(
        candidate.transcript().map_err(|error| error.to_string())?,
        VOLTA_2_RUNTIME_REBIND_TRANSCRIPT
    );
    Ok(())
}

#[test]
fn key_order_and_whitespace_do_not_change_identity() -> Result<(), String> {
    let original = Risc0RouteBManifestVectorV1::from_json(VECTOR)
        .map_err(|error| error.to_string())?
        .compute()
        .map_err(|error| error.to_string())?;
    let value: Value = serde_json::from_str(VECTOR).map_err(|error| error.to_string())?;
    let reordered = parse_vector(&value)?
        .compute()
        .map_err(|error| error.to_string())?;
    assert_eq!(original.canonical_bytes, reordered.canonical_bytes);
    assert_eq!(original.route_id, reordered.route_id);
    Ok(())
}

#[test]
fn every_static_manifest_leaf_changes_identity_or_fails_closed() -> Result<(), String> {
    let base_value: Value = serde_json::from_str(VECTOR).map_err(|error| error.to_string())?;
    let base_id = parse_vector(&base_value)?
        .compute()
        .map_err(|error| error.to_string())?
        .route_id;
    let manifest = &base_value["manifest"];
    let mut paths = Vec::new();
    leaf_paths(manifest, &mut Vec::new(), &mut paths);
    assert_eq!(
        paths.len(),
        65,
        "new static leaves require an explicit mutation gate"
    );

    for path in paths {
        let mut mutated = base_value.clone();
        let target = value_mut(&mut mutated["manifest"], &path);
        mutate_leaf(target)?;
        if let Ok(parsed) = parse_vector(&mutated) {
            let mutated_id = parsed
                .compute()
                .map_err(|error| error.to_string())?
                .route_id;
            assert_ne!(
                mutated_id, base_id,
                "mutation did not change route ID: {path:?}"
            );
        }
    }
    Ok(())
}

#[test]
fn malformed_json_shapes_and_hex_fail_closed() -> Result<(), String> {
    let base: Value = serde_json::from_str(VECTOR).map_err(|error| error.to_string())?;

    let mut missing = base.clone();
    let _ = object_mut(&mut missing, &["manifest", "source_network"])?.remove("genesis_hash");
    assert!(parse_vector(&missing).is_err());

    let mut unknown = base.clone();
    object_mut(&mut unknown, &["manifest"])?.insert("unexpected".to_owned(), json!(1));
    assert!(parse_vector(&unknown).is_err());

    let duplicate = VECTOR.replacen(
        "\"manifest_version\": 1,",
        "\"manifest_version\": 1, \"manifest_version\": 1,",
        1,
    );
    assert!(Risc0RouteBManifestVectorV1::from_json(&duplicate).is_err());

    let mut bad_width = base.clone();
    bad_width["manifest"]["destination"]["gateway_proxy"] = json!("0x00");
    assert!(parse_vector(&bad_width).is_err());

    let mut uppercase = base.clone();
    uppercase["manifest"]["destination"]["gateway_proxy"] =
        json!("0x0807C544d38ae7729f8798388d89be6502a1e8a8");
    assert!(parse_vector(&uppercase).is_err());
    Ok(())
}

#[test]
fn non_integer_and_out_of_range_numbers_fail_closed() -> Result<(), String> {
    let base: Value = serde_json::from_str(VECTOR).map_err(|error| error.to_string())?;
    for invalid in [
        json!("2"),
        json!(2.0),
        json!(true),
        json!(-1),
        json!(4294967296_u64),
    ] {
        let mut mutated = base.clone();
        mutated["manifest"]["aggregation_domain_id"] = invalid;
        assert!(parse_vector(&mutated).is_err());
    }
    let mut action = base;
    action["settlement_key_sample"]["action_kind"] = json!(3);
    assert!(parse_vector(&action).is_err());
    Ok(())
}

#[test]
fn manifest_rotation_does_not_change_the_settlement_key() -> Result<(), String> {
    let base: Value = serde_json::from_str(VECTOR).map_err(|error| error.to_string())?;
    let original = parse_vector(&base)?
        .compute()
        .map_err(|error| error.to_string())?;
    let mut rotated = base;
    rotated["manifest"]["destination"]["gateway_proxy_code_hash"] =
        json!("0x614b3810e962f850c014b1e2d138ade358edb749d37432076e06dcb9abe702b8");
    let changed = parse_vector(&rotated)?
        .compute()
        .map_err(|error| error.to_string())?;
    assert_ne!(original.route_id, changed.route_id);
    assert_eq!(
        original.settlement_key_preimage,
        changed.settlement_key_preimage
    );
    assert_eq!(original.settlement_key, changed.settlement_key);
    Ok(())
}
