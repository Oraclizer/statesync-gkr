//! Direct native SMT predicate comparison, separate from GKR evidence.
use std::hint::black_box;
use std::time::Instant;
use statesync_gkr::compiler::{AssetId,LeafPayload,LeafState,MerklePath,PublicInputs,SmtOperation,SmtParams,SmtWitness,smt_valid_native};
use statesync_gkr::primitives::field::{BaseField,PrimeCharacteristicRing};
use statesync_gkr::primitives::hash::{Digest,HashGadget,Poseidon2Gadget};
use statesync_gkr::SyncRequest;
const SEED: u64 = 0x5353474b52202026;

fn argument(name: &str, default: &str) -> String {
    let xs: Vec<_> = std::env::args().collect();
    xs.windows(2).find(|x| x[0] == name).map(|x| x[1].clone()).unwrap_or_else(|| default.into())
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

fn field(state: &mut u64) -> BaseField {
    BaseField::from_u32((splitmix(state) & 0x00ff_ffff) as u32)
}

fn fixture(depth: u32, label: &str, index: usize) -> SyncRequest {
    let kind_tag = match label { "membership" => 0, "nonmembership" => 1, "update" => 2, _ => panic!("unknown kind") };
    let mut seed = SEED ^ ((depth as u64) << 32) ^ ((kind_tag as u64) << 56) ^ index as u64;
    // Unique keys within this cell and below the base-field alias boundary.
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

fn main() {
    let kind=argument("--kind","membership");
    let depth:u32=argument("--depth","24").parse().expect("depth");
    let run:usize=argument("--run","1").parse().expect("run");
    assert!([24,28,32].contains(&depth));
    assert!([1,2,3].contains(&run));
    let requests:Vec<_>=(0..768).map(|i|fixture(depth,&kind,i)).collect();
    let params=SmtParams{depth,..Default::default()};
    let hasher=Poseidon2Gadget::default();
    for request in &requests {
        assert!(smt_valid_native(&hasher,&params,&request.operation,&request.public_inputs.old_root,&request.public_inputs.new_root,&request.witness).expect("honest predicate"));
        let mut wrong_old=request.public_inputs.old_root;
        wrong_old.0[0]+=BaseField::ONE;
        assert!(!smt_valid_native(&hasher,&params,&request.operation,&wrong_old,&request.public_inputs.new_root,&request.witness).expect("wrong old root"));
        let mut wrong_new=request.public_inputs.new_root;
        wrong_new.0[0]+=BaseField::ONE;
        assert!(!smt_valid_native(&hasher,&params,&request.operation,&request.public_inputs.old_root,&wrong_new,&request.witness).expect("wrong new root"));
        let mut wrong_witness=request.witness.clone();
        wrong_witness.path.siblings[0].0[0]+=BaseField::ONE;
        assert!(!smt_valid_native(&hasher,&params,&request.operation,&request.public_inputs.old_root,&request.public_inputs.new_root,&wrong_witness).expect("wrong sibling"));
    }
    println!("scope,run,kind,depth,sample,elapsed_ns,accepted");
    for i in 0..1005 {
        let request=&requests[(i+run*67)%requests.len()];
        let start=Instant::now();
        let accepted=black_box(smt_valid_native(black_box(&hasher),black_box(&params),black_box(&request.operation),black_box(&request.public_inputs.old_root),black_box(&request.public_inputs.new_root),black_box(&request.witness))).expect("native predicate");
        let elapsed=start.elapsed().as_nanos();
        assert!(accepted);
        if i>=5 { println!("native_smt_validity,{run},{kind},{depth},{},{elapsed},true",i-5); }
    }
}