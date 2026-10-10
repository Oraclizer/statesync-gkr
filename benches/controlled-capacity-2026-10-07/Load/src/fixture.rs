// The immutable supplement's original constructor, reused without a new corpus.
use statesync_gkr::compiler::{AssetId, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation, SmtParams, SmtWitness};
use statesync_gkr::primitives::field::{BaseField, PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest, HashGadget, Poseidon2Gadget};
use statesync_gkr::SyncRequest;
pub const SEED: u64 = 0x5353474b52202026;

pub fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

pub fn field(state: &mut u64) -> BaseField {
    BaseField::from_u32((splitmix(state) & 0x00ff_ffff) as u32)
}

pub fn original(depth: u32, label: &str, index: usize) -> SyncRequest {
    let kind_tag = match label { "membership" => 0, "nonmembership" => 1, "update" => 2, _ => panic!("unknown kind") };
    let mut seed = SEED ^ ((depth as u64) << 32) ^ ((kind_tag as u64) << 56) ^ index as u64;
    let key = AssetId(index as u64 + 1);
    assert!(key.0 < 1u64 << depth.min(24));
    let path = MerklePath { siblings: (0..depth).map(|_| Digest(core::array::from_fn(|_| field(&mut seed)))).collect() };
    let identity: [u8; 32] = core::array::from_fn(|_| splitmix(&mut seed) as u8);
    let payload = LeafPayload { sync_state: vec![field(&mut seed), field(&mut seed)], identity_digest: identity };
    let occupied = LeafState::Occupied(payload.clone());
    let params = SmtParams { depth, ..Default::default() };
    let hasher = Poseidon2Gadget::default();
    let (operation, old_leaf, new_leaf) = match label {
        "membership" => (SmtOperation::Membership { key, payload }, occupied.clone(), occupied),
        "nonmembership" => (SmtOperation::NonMembership { key }, LeafState::Empty, LeafState::Empty),
        "update" => {
            let new_payload = LeafPayload { sync_state: vec![field(&mut seed), field(&mut seed)], identity_digest: identity };
            let new_leaf = LeafState::Occupied(new_payload);
            (SmtOperation::Update { key, old_leaf: occupied.clone(), new_leaf: new_leaf.clone() }, occupied, new_leaf)
        }
        _ => unreachable!(),
    };
    let old_root = path.compute_root(&hasher, &params, key, &old_leaf).expect("valid old path");
    let new_root = path.compute_root(&hasher, &params, key, &new_leaf).expect("valid new path");
    let value_digest = hasher.hash_leaf(&new_leaf.encode()).expect("in-bound leaf encoding");
    SyncRequest {
        operation,
        witness: SmtWitness { leaf: old_leaf, path },
        public_inputs: PublicInputs { old_root, new_root, op_kind_tag: kind_tag, asset_id: key, value_digest },
    }
}
