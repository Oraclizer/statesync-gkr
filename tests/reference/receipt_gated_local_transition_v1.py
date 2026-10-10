#!/usr/bin/env python3
"""Independent standard-library codec for the local transition golden vector."""

import hashlib
import json
import struct
import sys


DOMAIN = b"SSGKR_RECEIPT_GATED_LOCAL_TRANSITION_V1"
PROFILE = "ssgkr/receipt-gated-local-transition/v1"


def reject_duplicates(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def require_keys(value, expected, label):
    actual = set(value)
    expected = set(expected)
    if actual != expected:
        raise ValueError(
            f"{label} keys differ: missing={sorted(expected - actual)}, "
            f"unknown={sorted(actual - expected)}"
        )


def fixed_hex(value, size, label, prefixed=False):
    if not isinstance(value, str):
        raise ValueError(f"{label} must be hex text")
    if prefixed:
        if not value.startswith("0x"):
            raise ValueError(f"{label} requires 0x")
        value = value[2:]
    if len(value) != size * 2 or value != value.lower():
        raise ValueError(f"{label} must be {size} lowercase hex bytes")
    try:
        return bytes.fromhex(value)
    except ValueError as error:
        raise ValueError(f"{label} is malformed hex") from error


def u16(value, label):
    if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value <= 0xFFFF:
        raise ValueError(f"{label} is not u16")
    return struct.pack(">H", value)


def u32(value, label):
    if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value <= 0xFFFFFFFF:
        raise ValueError(f"{label} is not u32")
    return struct.pack(">I", value)


def u64(value, label):
    if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value <= 0xFFFFFFFFFFFFFFFF:
        raise ValueError(f"{label} is not u64")
    return struct.pack(">Q", value)


def encode(vector):
    require_keys(
        vector,
        ["schema", "status", "profile", "versions", "frozen_inputs", "transition", "expected", "nonclaims"],
        "vector",
    )
    if vector["schema"] != "ssgkr/receipt-gated-local-transition-vector/v1":
        raise ValueError("wrong schema")
    if vector["status"] != "private-nondeployment-local-candidate" or vector["profile"] != PROFILE:
        raise ValueError("wrong claim ceiling")

    versions = vector["versions"]
    require_keys(versions, ["oip_semantic", "inner_proof", "transition_codec"], "versions")
    if versions["oip_semantic"] != [0, 5, 0]:
        raise ValueError("OIP semantic version is not 0.5.0")
    out = bytearray(DOMAIN)
    for index, value in enumerate(versions["oip_semantic"]):
        out += u16(value, f"oip_semantic[{index}]")
    out += u16(versions["inner_proof"], "inner_proof")
    out += u16(versions["transition_codec"], "transition_codec")

    anchors = vector["frozen_inputs"]
    anchor_fields = [
        ("product_commit", 20),
        ("product_tree", 20),
        ("readiness_index_sha256", 32),
        ("a14_report_sha256", 32),
        ("a14_manifest_sha256", 32),
        ("evm_commit", 20),
        ("evm_tree", 20),
        ("lifecycle_evidence_sha256", 32),
        ("lifecycle_vector_sha256", 32),
        ("route_vector_sha256", 32),
        ("destination_vector_sha256", 32),
    ]
    require_keys(anchors, [field for field, _ in anchor_fields], "frozen_inputs")
    for field, size in anchor_fields:
        out += fixed_hex(anchors[field], size, field)

    transition = vector["transition"]
    transition_fields = [
        "route_id", "program_binary_size", "program_binary_sha256", "image_id",
        "raw_guest_elf_sha256", "raw192_sha256", "statement_leaf",
        "primary_finality_record_id", "primary_finality_committed", "source_network_id",
        "destination_chain_id", "destination_consumer", "domain_id", "aggregation_id",
        "leaf_count", "leaf_index", "merkle_path", "authenticated_receipt_root", "lifecycle",
        "claim_id", "settlement_key", "expected_predecessor", "next_application_state",
    ]
    require_keys(transition, transition_fields, "transition")
    out += fixed_hex(transition["route_id"], 32, "route_id")
    out += u64(transition["program_binary_size"], "program_binary_size")
    for field in [
        "program_binary_sha256", "image_id", "raw_guest_elf_sha256", "raw192_sha256",
        "statement_leaf", "primary_finality_record_id",
    ]:
        out += fixed_hex(transition[field], 32, field)
    if not isinstance(transition["primary_finality_committed"], bool):
        raise ValueError("primary_finality_committed must be boolean")
    out += bytes([int(transition["primary_finality_committed"])])
    out += fixed_hex(transition["source_network_id"], 32, "source_network_id")
    out += u64(transition["destination_chain_id"], "destination_chain_id")
    out += fixed_hex(transition["destination_consumer"], 32, "destination_consumer")
    out += u32(transition["domain_id"], "domain_id")
    out += u64(transition["aggregation_id"], "aggregation_id")
    out += u32(transition["leaf_count"], "leaf_count")
    out += u32(transition["leaf_index"], "leaf_index")
    path = transition["merkle_path"]
    if not isinstance(path, list) or len(path) > 0xFFFF:
        raise ValueError("merkle_path is not a bounded list")
    out += u16(len(path), "merkle_path length")
    for index, sibling in enumerate(path):
        out += fixed_hex(sibling, 32, f"merkle_path[{index}]")
    out += fixed_hex(transition["authenticated_receipt_root"], 32, "authenticated_receipt_root")

    lifecycle = transition["lifecycle"]
    lifecycle_fields = [
        "status", "current_revision", "registered_revision", "draining_from_revision",
        "registered_at_block", "drain_started_at_block", "consume_until_block",
        "destination_block", "lineage_abandoned", "replacement_route_id",
    ]
    require_keys(lifecycle, lifecycle_fields, "lifecycle")
    statuses = {"active": 1, "draining": 2, "revoked": 3, "replaced": 4}
    if lifecycle["status"] not in statuses:
        raise ValueError("unknown lifecycle status")
    out += bytes([statuses[lifecycle["status"]]])
    for field in lifecycle_fields[1:8]:
        out += u64(lifecycle[field], field)
    if not isinstance(lifecycle["lineage_abandoned"], bool):
        raise ValueError("lineage_abandoned must be boolean")
    out += bytes([int(lifecycle["lineage_abandoned"])])
    out += fixed_hex(lifecycle["replacement_route_id"], 32, "replacement_route_id")
    for field in ["claim_id", "settlement_key", "expected_predecessor", "next_application_state"]:
        out += fixed_hex(transition[field], 32, field)
    return bytes(out)


def main():
    if len(sys.argv) != 2:
        raise ValueError("usage: receipt_gated_local_transition_v1.py <vector>")
    with open(sys.argv[1], "r", encoding="utf-8") as handle:
        vector = json.load(handle, object_pairs_hook=reject_duplicates)
    canonical = encode(vector)
    candidate = hashlib.sha256(canonical).digest()
    expected = vector["expected"]
    require_keys(expected, ["canonical_bytes", "candidate_id", "secondary_finalized", "selected_cdk_backend"], "expected")
    if canonical != fixed_hex(expected["canonical_bytes"], len(canonical), "canonical_bytes", prefixed=True):
        raise ValueError("canonical bytes differ from golden value")
    if candidate != fixed_hex(expected["candidate_id"], 32, "candidate_id", prefixed=True):
        raise ValueError("candidate ID differs from golden value")
    if expected["secondary_finalized"] is not False or expected["selected_cdk_backend"] != "NOT SET":
        raise ValueError("claim ceiling changed")
    transcript = "\n".join([
        f"profile={PROFILE}",
        "oip_semantic_version=0.5.0",
        f"canonical_bytes=0x{canonical.hex()}",
        f"candidate_id=0x{candidate.hex()}",
        "",
    ])
    sys.stdout.buffer.write(transcript.encode("ascii"))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
