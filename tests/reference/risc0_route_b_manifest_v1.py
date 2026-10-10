#!/usr/bin/env python3
"""Independent standard-library Route B parser, codec, and hash transcript."""

from __future__ import annotations

import hashlib
import json
import struct
import sys
from pathlib import Path
from typing import Any


ROUTE_DOMAIN = b"ssgkr/risc0-route-b-manifest/v1"
SETTLEMENT_DOMAIN = b"ssgkr/settlement-key/v1"
MASK64 = (1 << 64) - 1
ROTATION = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)
ROUND_CONSTANTS = (
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
)


class ManifestError(ValueError):
    """A strict parsing or semantic-validation failure."""


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ManifestError(f"duplicate key: {key}")
        result[key] = value
    return result


def exact_keys(value: Any, required: set[str], path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ManifestError(f"{path} must be an object")
    actual = set(value)
    if actual != required:
        raise ManifestError(
            f"{path} keys differ; missing={sorted(required - actual)}, "
            f"unknown={sorted(actual - required)}"
        )
    return value


def integer(value: Any, bits: int, path: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ManifestError(f"{path} must be a JSON integer")
    if value < 0 or value >= 1 << bits:
        raise ManifestError(f"{path} is outside u{bits}")
    return value


def boolean(value: Any, path: str) -> bool:
    if not isinstance(value, bool):
        raise ManifestError(f"{path} must be a JSON boolean")
    return value


def text(value: Any, path: str) -> str:
    if not isinstance(value, str) or not value:
        raise ManifestError(f"{path} must be a non-empty string")
    if len(value.encode("utf-8")) > 0xFFFF:
        raise ManifestError(f"{path} exceeds u16 UTF-8 length")
    return value


def fixed_text(value: Any, expected: str, path: str) -> str:
    actual = text(value, path)
    if actual != expected:
        raise ManifestError(f"unsupported {path}: {actual}")
    return actual


def fixed_integer(value: Any, expected: int, bits: int, path: str) -> int:
    actual = integer(value, bits, path)
    if actual != expected:
        raise ManifestError(f"{path} must be {expected}")
    return actual


def lower_hex(value: Any, size: int, path: str) -> bytes:
    if not isinstance(value, str) or not value.startswith("0x"):
        raise ManifestError(f"{path} must start with lowercase 0x")
    digits = value[2:]
    if len(digits) != size * 2 or any(c not in "0123456789abcdef" for c in digits):
        raise ManifestError(f"{path} must be exactly {size} lowercase-hex bytes")
    return bytes.fromhex(digits)


def tagged(value: Any, expected: str, path: str) -> bytes:
    fixed_text(value, expected, path)
    return b"\x01"


def string_bytes(value: Any, path: str) -> bytes:
    encoded = text(value, path).encode("utf-8")
    return struct.pack("<H", len(encoded)) + encoded


def bool_byte(value: Any, path: str) -> bytes:
    return bytes((1 if boolean(value, path) else 0,))


def rotate_left(value: int, count: int) -> int:
    if count == 0:
        return value & MASK64
    return ((value << count) | (value >> (64 - count))) & MASK64


def keccak_f1600(state: list[int]) -> None:
    for round_constant in ROUND_CONSTANTS:
        columns = [
            state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
            for x in range(5)
        ]
        deltas = [
            columns[(x - 1) % 5] ^ rotate_left(columns[(x + 1) % 5], 1)
            for x in range(5)
        ]
        for y in range(5):
            for x in range(5):
                state[x + 5 * y] ^= deltas[x]
        moved = [0] * 25
        for y in range(5):
            for x in range(5):
                moved[y + 5 * ((2 * x + 3 * y) % 5)] = rotate_left(
                    state[x + 5 * y], ROTATION[x][y]
                )
        for y in range(5):
            row = [moved[x + 5 * y] for x in range(5)]
            for x in range(5):
                state[x + 5 * y] = (
                    row[x] ^ ((~row[(x + 1) % 5]) & row[(x + 2) % 5])
                ) & MASK64
        state[0] ^= round_constant


def keccak256(data: bytes) -> bytes:
    rate = 136
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate != rate - 1:
        padded.append(0)
    padded.append(0x80)
    state = [0] * 25
    for offset in range(0, len(padded), rate):
        block = padded[offset : offset + rate]
        for lane in range(rate // 8):
            state[lane] ^= int.from_bytes(block[lane * 8 : lane * 8 + 8], "little")
        keccak_f1600(state)
    return b"".join(lane.to_bytes(8, "little") for lane in state)[:32]


def encode_manifest(manifest: Any) -> tuple[bytes, dict[str, Any]]:
    m = exact_keys(
        manifest,
        {
            "manifest_version", "route_family", "proof_system", "source_network",
            "verifier", "statement", "aggregation_domain_id", "destination",
            "trust", "transport", "conflict", "settlement_key", "receipt_tuple",
        },
        "manifest",
    )
    source = exact_keys(
        m["source_network"],
        {
            "network_name", "genesis_hash", "runtime_spec_name",
            "runtime_spec_version", "runtime_transaction_version",
            "runtime_state_version", "runtime_source_tag", "runtime_source_commit",
        },
        "manifest.source_network",
    )
    verifier = exact_keys(
        m["verifier"],
        {
            "risc0_release", "risc0_source_commit", "guest_toolchain",
            "guest_elf_sha256", "verification_context", "verifier_version_preimage",
            "verifier_version_hash", "image_id", "image_id_encoding",
            "zkverify_vk_semantics",
        },
        "manifest.verifier",
    )
    statement = exact_keys(
        m["statement"],
        {
            "application_statement_version", "raw_statement_encoding",
            "raw_statement_bytes", "public_values_semantics",
            "circuit_commitment_binding", "native_statement_formula",
        },
        "manifest.statement",
    )
    destination = exact_keys(
        m["destination"],
        {
            "network_name", "chain_id", "gateway_proxy", "gateway_proxy_code_hash",
            "gateway_implementation", "gateway_implementation_code_hash",
        },
        "manifest.destination",
    )
    trust = exact_keys(
        m["trust"],
        {
            "role_model", "observed_publisher", "observed_publisher_capability",
            "upgrader_capability", "default_admin_capability",
            "upgrader_principal_pinned", "default_admin_principal_pinned",
            "proxy_is_upgradeable", "proxy_and_implementation_are_tcb",
        },
        "manifest.trust",
    )
    transport = exact_keys(
        m["transport"],
        {"authentication", "destination_verifies_volta_grandpa_finality", "source_finality_policy"},
        "manifest.transport",
    )
    conflict = exact_keys(
        m["conflict"],
        {"same_coordinate_overwrite_possible", "conflict_rejection", "enforcement_owner"},
        "manifest.conflict",
    )
    settlement = exact_keys(
        m["settlement_key"],
        {
            "domain", "hash_algorithm", "preimage_order",
            "primary_transition_id_bytes", "destination_chain_id_encoding",
            "destination_consumer_bytes", "action_kind_encoding", "includes_route_id",
        },
        "manifest.settlement_key",
    )
    receipt = exact_keys(
        m["receipt_tuple"],
        {
            "domain_id_encoding", "aggregation_id_encoding", "leaf_count_encoding",
            "leaf_index_encoding", "merkle_path_node_bytes",
            "canonical_relation_required", "live_enforcement", "enforcement_owner",
        },
        "manifest.receipt_tuple",
    )

    version_preimage = text(
        verifier["verifier_version_preimage"],
        "manifest.verifier.verifier_version_preimage",
    )
    version_hash = lower_hex(
        verifier["verifier_version_hash"], 32, "manifest.verifier.verifier_version_hash"
    )
    if hashlib.sha256(version_preimage.encode()).digest() != version_hash:
        raise ManifestError("verifier_version_hash does not match verifier_version_preimage")

    out = bytearray()
    out += struct.pack("<H", fixed_integer(m["manifest_version"], 1, 16, "manifest.manifest_version"))
    out += tagged(m["route_family"], "risc0-native-zkverify", "manifest.route_family")
    out += tagged(m["proof_system"], "risc0-receipt-v3", "manifest.proof_system")
    out += string_bytes(source["network_name"], "manifest.source_network.network_name")
    out += lower_hex(source["genesis_hash"], 32, "manifest.source_network.genesis_hash")
    out += string_bytes(source["runtime_spec_name"], "manifest.source_network.runtime_spec_name")
    out += struct.pack("<I", integer(source["runtime_spec_version"], 32, "manifest.source_network.runtime_spec_version"))
    out += struct.pack("<I", integer(source["runtime_transaction_version"], 32, "manifest.source_network.runtime_transaction_version"))
    out += bytes((integer(source["runtime_state_version"], 8, "manifest.source_network.runtime_state_version"),))
    out += string_bytes(source["runtime_source_tag"], "manifest.source_network.runtime_source_tag")
    out += lower_hex(source["runtime_source_commit"], 20, "manifest.source_network.runtime_source_commit")
    out += string_bytes(verifier["risc0_release"], "manifest.verifier.risc0_release")
    out += lower_hex(verifier["risc0_source_commit"], 20, "manifest.verifier.risc0_source_commit")
    out += string_bytes(verifier["guest_toolchain"], "manifest.verifier.guest_toolchain")
    out += lower_hex(verifier["guest_elf_sha256"], 32, "manifest.verifier.guest_elf_sha256")
    context = fixed_text(verifier["verification_context"], "risc0", "manifest.verifier.verification_context")
    out += string_bytes(context, "manifest.verifier.verification_context")
    out += string_bytes(version_preimage, "manifest.verifier.verifier_version_preimage")
    out += version_hash
    image_id = lower_hex(verifier["image_id"], 32, "manifest.verifier.image_id")
    out += image_id
    out += tagged(verifier["image_id_encoding"], "eight-le-u32-words-concatenated-in-word-order", "manifest.verifier.image_id_encoding")
    out += tagged(verifier["zkverify_vk_semantics"], "image-id-bytes32", "manifest.verifier.zkverify_vk_semantics")
    out += struct.pack("<H", fixed_integer(statement["application_statement_version"], 1, 16, "manifest.statement.application_statement_version"))
    out += tagged(statement["raw_statement_encoding"], "wrap-statement-v1-six-bn254-le32", "manifest.statement.raw_statement_encoding")
    out += struct.pack("<H", fixed_integer(statement["raw_statement_bytes"], 192, 16, "manifest.statement.raw_statement_bytes"))
    out += tagged(statement["public_values_semantics"], "unframed-exact-raw192", "manifest.statement.public_values_semantics")
    out += tagged(statement["circuit_commitment_binding"], "raw192-bytes-32-63-le32", "manifest.statement.circuit_commitment_binding")
    out += tagged(statement["native_statement_formula"], "keccak256(context-keccak256||image-id||verifier-version-hash||raw192-keccak256)", "manifest.statement.native_statement_formula")
    out += struct.pack("<I", integer(m["aggregation_domain_id"], 32, "manifest.aggregation_domain_id"))
    out += string_bytes(destination["network_name"], "manifest.destination.network_name")
    out += struct.pack("<Q", integer(destination["chain_id"], 64, "manifest.destination.chain_id"))
    out += lower_hex(destination["gateway_proxy"], 20, "manifest.destination.gateway_proxy")
    out += lower_hex(destination["gateway_proxy_code_hash"], 32, "manifest.destination.gateway_proxy_code_hash")
    out += lower_hex(destination["gateway_implementation"], 20, "manifest.destination.gateway_implementation")
    out += lower_hex(destination["gateway_implementation_code_hash"], 32, "manifest.destination.gateway_implementation_code_hash")
    out += tagged(trust["role_model"], "capability-only", "manifest.trust.role_model")
    out += lower_hex(trust["observed_publisher"], 20, "manifest.trust.observed_publisher")
    out += tagged(trust["observed_publisher_capability"], "OPERATOR", "manifest.trust.observed_publisher_capability")
    out += tagged(trust["upgrader_capability"], "UPGRADER", "manifest.trust.upgrader_capability")
    out += tagged(trust["default_admin_capability"], "DEFAULT_ADMIN", "manifest.trust.default_admin_capability")
    out += bool_byte(trust["upgrader_principal_pinned"], "manifest.trust.upgrader_principal_pinned")
    out += bool_byte(trust["default_admin_principal_pinned"], "manifest.trust.default_admin_principal_pinned")
    out += bool_byte(trust["proxy_is_upgradeable"], "manifest.trust.proxy_is_upgradeable")
    out += bool_byte(trust["proxy_and_implementation_are_tcb"], "manifest.trust.proxy_and_implementation_are_tcb")
    out += tagged(transport["authentication"], "operator-authenticated", "manifest.transport.authentication")
    out += bool_byte(transport["destination_verifies_volta_grandpa_finality"], "manifest.transport.destination_verifies_volta_grandpa_finality")
    out += tagged(transport["source_finality_policy"], "not-enforced-by-destination", "manifest.transport.source_finality_policy")
    out += bool_byte(conflict["same_coordinate_overwrite_possible"], "manifest.conflict.same_coordinate_overwrite_possible")
    out += tagged(conflict["conflict_rejection"], "not-enforced", "manifest.conflict.conflict_rejection")
    out += tagged(conflict["enforcement_owner"], "destination-receiver", "manifest.conflict.enforcement_owner")
    settlement_domain = fixed_text(settlement["domain"], SETTLEMENT_DOMAIN.decode(), "manifest.settlement_key.domain")
    out += string_bytes(settlement_domain, "manifest.settlement_key.domain")
    out += tagged(settlement["hash_algorithm"], "sha256", "manifest.settlement_key.hash_algorithm")
    out += tagged(settlement["preimage_order"], "domain||primary-transition-id||destination-chain-id-le64||destination-consumer-bytes32||action-kind-u8", "manifest.settlement_key.preimage_order")
    out += bytes((fixed_integer(settlement["primary_transition_id_bytes"], 32, 8, "manifest.settlement_key.primary_transition_id_bytes"),))
    out += tagged(settlement["destination_chain_id_encoding"], "u64-le", "manifest.settlement_key.destination_chain_id_encoding")
    out += bytes((fixed_integer(settlement["destination_consumer_bytes"], 32, 8, "manifest.settlement_key.destination_consumer_bytes"),))
    out += tagged(settlement["action_kind_encoding"], "u8", "manifest.settlement_key.action_kind_encoding")
    if boolean(settlement["includes_route_id"], "manifest.settlement_key.includes_route_id"):
        raise ManifestError("manifest.settlement_key.includes_route_id must be false")
    out += b"\x00"
    out += tagged(receipt["domain_id_encoding"], "u32-le", "manifest.receipt_tuple.domain_id_encoding")
    out += tagged(receipt["aggregation_id_encoding"], "u64-le", "manifest.receipt_tuple.aggregation_id_encoding")
    out += tagged(receipt["leaf_count_encoding"], "u32-le", "manifest.receipt_tuple.leaf_count_encoding")
    out += tagged(receipt["leaf_index_encoding"], "u32-le", "manifest.receipt_tuple.leaf_index_encoding")
    out += bytes((fixed_integer(receipt["merkle_path_node_bytes"], 32, 8, "manifest.receipt_tuple.merkle_path_node_bytes"),))
    out += bool_byte(receipt["canonical_relation_required"], "manifest.receipt_tuple.canonical_relation_required")
    out += tagged(receipt["live_enforcement"], "not-enforced", "manifest.receipt_tuple.live_enforcement")
    out += tagged(receipt["enforcement_owner"], "destination-receiver", "manifest.receipt_tuple.enforcement_owner")
    return bytes(out), {"context": context, "image_id": image_id, "version_hash": version_hash}


def compute(vector: Any) -> str:
    top = exact_keys(
        vector,
        {"vector_version", "manifest", "statement_sample", "settlement_key_sample"},
        "vector",
    )
    fixed_integer(top["vector_version"], 1, 16, "vector.vector_version")
    canonical, parsed = encode_manifest(top["manifest"])
    statement = exact_keys(top["statement_sample"], {"raw192"}, "vector.statement_sample")
    raw192 = lower_hex(statement["raw192"], 192, "vector.statement_sample.raw192")
    settlement = exact_keys(
        top["settlement_key_sample"],
        {
            "primary_transition_id", "intended_destination_chain_id",
            "intended_destination_consumer", "action_kind",
        },
        "vector.settlement_key_sample",
    )
    primary_id = lower_hex(settlement["primary_transition_id"], 32, "vector.settlement_key_sample.primary_transition_id")
    destination_chain_id = integer(settlement["intended_destination_chain_id"], 64, "vector.settlement_key_sample.intended_destination_chain_id")
    destination_consumer = lower_hex(settlement["intended_destination_consumer"], 32, "vector.settlement_key_sample.intended_destination_consumer")
    action_kind = integer(settlement["action_kind"], 8, "vector.settlement_key_sample.action_kind")
    if action_kind > 2:
        raise ManifestError("vector.settlement_key_sample.action_kind must be 0, 1, or 2")

    context_bytes = parsed["context"].encode()
    context_hash = keccak256(context_bytes)
    raw_sha = hashlib.sha256(raw192).digest()
    raw_keccak = keccak256(raw192)
    statement_preimage = context_hash + parsed["image_id"] + parsed["version_hash"] + raw_keccak
    native_statement = keccak256(statement_preimage)
    settlement_preimage = (
        SETTLEMENT_DOMAIN + primary_id + struct.pack("<Q", destination_chain_id)
        + destination_consumer + bytes((action_kind,))
    )
    values = (
        ("profile", "risc0-route-b-manifest-v1"),
        ("route_id_domain_utf8", ROUTE_DOMAIN.decode()),
        ("canonical_bytes_length", str(len(canonical))),
        ("canonical_bytes", "0x" + canonical.hex()),
        ("route_id", "0x" + hashlib.sha256(ROUTE_DOMAIN + canonical).hexdigest()),
        ("verification_context_utf8", parsed["context"]),
        ("verification_context_keccak256", "0x" + context_hash.hex()),
        ("image_id", "0x" + parsed["image_id"].hex()),
        ("verifier_version_hash", "0x" + parsed["version_hash"].hex()),
        ("raw192_sha256", "0x" + raw_sha.hex()),
        ("raw192_keccak256", "0x" + raw_keccak.hex()),
        ("native_statement_preimage", "0x" + statement_preimage.hex()),
        ("native_statement", "0x" + native_statement.hex()),
        ("settlement_key_domain_utf8", SETTLEMENT_DOMAIN.decode()),
        ("settlement_key_preimage", "0x" + settlement_preimage.hex()),
        ("settlement_key", "0x" + hashlib.sha256(settlement_preimage).hexdigest()),
        ("settlement_key_includes_route_id", "false"),
        ("destination_enforcement_claim", "none"),
    )
    return "".join(f"{name}={value}\n" for name, value in values)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: risc0_route_b_manifest_v1.py PATH-TO-VECTOR", file=sys.stderr)
        return 2
    try:
        raw = Path(sys.argv[1]).read_text(encoding="utf-8")
        vector = json.loads(raw, object_pairs_hook=reject_duplicate_pairs)
        sys.stdout.buffer.write(compute(vector).encode("ascii"))
    except (OSError, json.JSONDecodeError, ManifestError, UnicodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
