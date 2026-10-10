use crate::fixture::{field, SEED};
use statesync_gkr::compiler::{AssetId, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation, SmtParams, SmtWitness};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::SyncRequest;

pub const NAMES: [&str; 8] = ["tombstone_nonmembership", "empty_to_occupied", "occupied_to_tombstone", "tombstone_to_occupied", "zero_payload_member", "max_payload_member", "root_chain_update", "large_key_member"];

fn occupied(seed: &mut u64, fields: usize) -> LeafState {
    LeafState::Occupied(LeafPayload { sync_state: (0..fields).map(|_| field(seed)).collect(), identity_digest: core::array::from_fn(|_| crate::fixture::splitmix(seed) as u8) })
}

fn request(key: AssetId, path: MerklePath, old: LeafState, new: LeafState, kind: &str) -> SyncRequest {
    let params = SmtParams { depth: 24, ..Default::default() };
    let hasher = Poseidon2Gadget::new(params.leaf_max_fields as usize);
    let operation = match kind {
        "membership" => {
            let LeafState::Occupied(payload) = &new else { panic!("membership leaf") };
            SmtOperation::Membership { key, payload: payload.clone() }
        }
        "nonmembership" => SmtOperation::NonMembership { key },
        "update" => SmtOperation::Update { key, old_leaf: old.clone(), new_leaf: new.clone() },
        _ => panic!("unsupported fixture kind"),
    };
    let old_root = path.compute_root(&hasher, &params, key, &old).expect("old root");
    let new_root = path.compute_root(&hasher, &params, key, &new).expect("new root");
    let value_digest = hasher.hash_leaf(&new.encode()).expect("bounded leaf");
    let tag = PublicInputs::kind_tag(operation.kind());
    SyncRequest { operation, witness: SmtWitness { leaf: old, path }, public_inputs: PublicInputs { old_root, new_root, op_kind_tag: tag, asset_id: key, value_digest } }
}

pub fn construct(name: &str, count: usize) -> Vec<SyncRequest> {
    let tag = NAMES.iter().position(|label| *label == name).expect("fixture type") as u64;
    let mut seed = SEED ^ 0x435f56415249414e ^ (tag << 40);
    if name == "root_chain_update" {
        let key = AssetId(41);
        let path = MerklePath { siblings: (0..24).map(|_| Digest(core::array::from_fn(|_| field(&mut seed)))).collect() };
        let mut old = occupied(&mut seed, 2);
        let mut requests: Vec<SyncRequest> = Vec::with_capacity(count);
        for _ in 0..count {
            let new = occupied(&mut seed, 2);
            let next = request(key, path.clone(), old, new.clone(), "update");
            if let Some(previous) = requests.last() {
                assert_eq!(previous.public_inputs.new_root, next.public_inputs.old_root, "broken root chain");
                assert_eq!(previous.public_inputs.asset_id, next.public_inputs.asset_id);
                assert_eq!(previous.witness.path.siblings, next.witness.path.siblings);
            }
            requests.push(next);
            old = new;
        }
        return requests;
    }
    (0..count).map(|index| {
        let key = AssetId(if name == "large_key_member" { (1u64 << 23) + index as u64 } else { index as u64 + 1 });
        assert!(key.0 < 1u64 << 24);
        let path = MerklePath { siblings: (0..24).map(|_| Digest(core::array::from_fn(|_| field(&mut seed)))).collect() };
        let (old, new, kind) = match name {
            "tombstone_nonmembership" => (LeafState::Tombstone, LeafState::Tombstone, "nonmembership"),
            "empty_to_occupied" => (LeafState::Empty, occupied(&mut seed, 2), "update"),
            "occupied_to_tombstone" => (occupied(&mut seed, 2), LeafState::Tombstone, "update"),
            "tombstone_to_occupied" => (LeafState::Tombstone, occupied(&mut seed, 2), "update"),
            "zero_payload_member" => { let leaf = occupied(&mut seed, 0); (leaf.clone(), leaf, "membership") },
            "max_payload_member" => { let leaf = occupied(&mut seed, 21); assert_eq!(leaf.encode().len(),31); (leaf.clone(), leaf, "membership") },
            "large_key_member" => { let leaf = occupied(&mut seed, 2); (leaf.clone(), leaf, "membership") },
            _ => panic!("unsupported fixture type"),
        };
        request(key, path, old, new, kind)
    }).collect()
}
