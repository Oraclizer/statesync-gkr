use serde::{Deserialize, Serialize};
use std::io::{self, Read, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use statesync_gkr::{SyncRequest, compiler::{AssetId, LeafPayload, LeafState, MerklePath, PublicInputs, SmtOperation, SmtWitness}};
use statesync_gkr::primitives::{field::{BaseField, PrimeCharacteristicRing, PrimeField32}, hash::Digest};

pub const PROTOCOL: u32 = 1;
pub const MAX_JSON: usize = 2 * 1024 * 1024;
pub const MAX_PROOF: usize = 16 * 1024 * 1024;

#[derive(Clone, Serialize, Deserialize)]
pub struct Leaf { pub tag: u8, pub payload: Vec<u32>, pub identity: [u8; 32] }
impl Leaf {
    fn from_leaf(x: &LeafState) -> Self {
        match x {
            LeafState::Empty => Self { tag: 0, payload: vec![], identity: [0;32] },
            LeafState::Tombstone => Self { tag: 2, payload: vec![], identity: [0;32] },
            LeafState::Occupied(p) => Self { tag: 1, payload: p.sync_state.iter().map(|x| x.as_canonical_u32()).collect(), identity: p.identity_digest },
        }
    }
    fn leaf(&self) -> Result<LeafState, String> {
        if self.payload.len() > 21 { return Err("payload exceeds measured profile".into()); }
        match self.tag {
            0 | 2 if self.payload.is_empty() && self.identity == [0;32] => Ok(if self.tag == 0 { LeafState::Empty } else { LeafState::Tombstone }),
            1 => Ok(LeafState::Occupied(LeafPayload { sync_state: self.payload.iter().map(|x| fe(*x)).collect::<Result<_,_>>()?, identity_digest: self.identity })),
            _ => Err("invalid leaf tag/fields".into()),
        }
    }
}
fn fe(x: u32) -> Result<BaseField, String> {
    if x >= BaseField::ORDER_U32 { Err("noncanonical input field".into()) } else { Ok(BaseField::from_u32(x)) }
}
fn digest(x: &[u32;8]) -> Result<Digest<BaseField>, String> {
    let mut out = [BaseField::ZERO;8];
    for (a,b) in out.iter_mut().zip(x) { *a = fe(*b)?; }
    Ok(Digest(out))
}
fn residues(x: &Digest<BaseField>) -> [u32;8] { core::array::from_fn(|i| x.0[i].as_canonical_u32()) }

#[derive(Clone, Serialize, Deserialize)]
pub struct Input {
    pub kind: String, pub key: u64, pub old_leaf: Leaf, pub new_leaf: Leaf,
    pub siblings: Vec<[u32;8]>, pub old_root: [u32;8], pub new_root: [u32;8], pub value_digest: [u32;8],
}
impl Input {
    pub fn from_request(r: &SyncRequest) -> Self {
        let (kind,new) = match &r.operation {
            SmtOperation::Membership { .. } => ("membership", &r.witness.leaf),
            SmtOperation::NonMembership { .. } => ("nonmembership", &r.witness.leaf),
            SmtOperation::Update { new_leaf, .. } => ("update", new_leaf),
        };
        Self { kind: kind.into(), key: r.public_inputs.asset_id.0, old_leaf: Leaf::from_leaf(&r.witness.leaf), new_leaf: Leaf::from_leaf(new), siblings: r.witness.path.siblings.iter().map(residues).collect(), old_root: residues(&r.public_inputs.old_root), new_root: residues(&r.public_inputs.new_root), value_digest: residues(&r.public_inputs.value_digest) }
    }
    pub fn request(&self, depth: u32) -> Result<SyncRequest,String> {
        if self.siblings.len() != depth as usize || depth == 0 || depth > 32 || self.key >= (1u64 << depth.min(24)) { return Err("input outside measured profile".into()); }
        let old = self.old_leaf.leaf()?; let new = self.new_leaf.leaf()?; let key = AssetId(self.key);
        let (tag,operation) = match self.kind.as_str() {
            "membership" => {
                if self.old_leaf.tag != 1 || serde_json::to_vec(&self.old_leaf).ok() != serde_json::to_vec(&self.new_leaf).ok() { return Err("invalid membership leaves".into()); }
                let LeafState::Occupied(p) = old.clone() else { return Err("membership payload missing".into()); };
                (0,SmtOperation::Membership { key, payload: p })
            }
            "nonmembership" => {
                if !matches!(self.old_leaf.tag,0|2) || serde_json::to_vec(&self.old_leaf).ok() != serde_json::to_vec(&self.new_leaf).ok() { return Err("invalid absence leaves".into()); }
                (1,SmtOperation::NonMembership { key })
            }
            "update" => (2,SmtOperation::Update { key, old_leaf: old.clone(), new_leaf: new }),
            _ => return Err("unknown operation kind".into()),
        };
        Ok(SyncRequest { operation, witness: SmtWitness { leaf: old, path: MerklePath { siblings: self.siblings.iter().map(digest).collect::<Result<_,_>>()? } }, public_inputs: PublicInputs { old_root: digest(&self.old_root)?, new_root: digest(&self.new_root)?, value_digest: digest(&self.value_digest)?, asset_id: key, op_kind_tag: tag } })
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Job {
    pub protocol: u32, pub run_id: String, pub job_id: u64, pub fixture_id: usize,
    pub repeat: usize, pub warmup: bool, pub scheduled_unix_ns: u64, pub deadline_unix_ns: u64, pub input: Input,
}
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Reply {
    pub protocol: u32, pub run_id: String, pub job_id: u64, pub fixture_id: usize,
    pub kind: String, pub host_id: String, pub process_id: u32, pub batch_id: u64, pub batch_size: usize,
    pub server_received_unix_ns: u64, pub server_enqueued_unix_ns: u64, pub flush_unix_ns: u64,
    pub witness_start_unix_ns: u64, pub witness_end_unix_ns: u64, pub prove_end_unix_ns: u64, pub encode_end_unix_ns: u64,
    pub server_send_start_unix_ns: u64, pub server_queue_ns: u64, pub batch_witness_ns: u64, pub batch_prove_ns: u64, pub batch_encode_ns: u64,
    pub encoded_bytes: usize, pub canonical_sha256: String, pub error: Option<String>,
}

pub fn write_request(out: &mut impl Write, job: &Job) -> io::Result<usize> {
    let data = serde_json::to_vec(job).map_err(io::Error::other)?;
    if data.len() > MAX_JSON { return Err(io::Error::other("request frame too large")); }
    out.write_all(&(data.len() as u32).to_be_bytes())?; out.write_all(&data)?;
    Ok(data.len()+4)
}
pub fn write_reply(out: &mut impl Write, reply: &Reply, proof: &[u8]) -> io::Result<usize> {
    let data = serde_json::to_vec(reply).map_err(io::Error::other)?;
    if data.len() > MAX_JSON || proof.len() > MAX_PROOF || proof.len() != reply.encoded_bytes { return Err(io::Error::other("reply frame bounds/length")); }
    out.write_all(&(data.len() as u32).to_be_bytes())?; out.write_all(&data)?;
    out.write_all(&(proof.len() as u32).to_be_bytes())?; out.write_all(proof)?;
    Ok(data.len()+proof.len()+8)
}
fn exact(input: &mut impl Read, buf: &mut [u8], stop: &AtomicBool) -> io::Result<(u64,u64)> {
    let mut offset = 0;
    let mut first=None;
    while offset < buf.len() {
        if stop.load(Ordering::Relaxed) { return Err(io::Error::new(io::ErrorKind::Interrupted,"driver stopping")); }
        match input.read(&mut buf[offset..]) {
            Ok(0) => return Err(io::Error::new(io::ErrorKind::UnexpectedEof,"peer closed frame")),
            Ok(n) => { first.get_or_insert(crate::shared::now()); offset += n; },
            Err(e) if matches!(e.kind(),io::ErrorKind::WouldBlock|io::ErrorKind::TimedOut|io::ErrorKind::Interrupted) => {},
            Err(e) => return Err(e),
        }
    }
    let end=crate::shared::now(); Ok((first.unwrap_or(end),end))
}
fn length(input: &mut impl Read, bound: usize, stop: &AtomicBool) -> io::Result<(usize,u64,u64)> {
    let mut bytes=[0;4]; let (first,end)=exact(input,&mut bytes,stop)?; let n=u32::from_be_bytes(bytes) as usize;
    if n>bound { Err(io::Error::other("frame exceeds bound")) } else { Ok((n,first,end)) }
}
pub fn read_request(input: &mut impl Read, stop: &AtomicBool) -> io::Result<(Job,u64,usize,u64)> {
    let (n,_,_)=length(input,MAX_JSON,stop)?; let mut bytes=vec![0;n]; let (_,end)=exact(input,&mut bytes,stop)?;
    let t=std::time::Instant::now(); let job=serde_json::from_slice(&bytes).map_err(io::Error::other)?;
    Ok((job,end,n+4,crate::shared::ns(t.elapsed())))
}
pub fn read_reply(input: &mut impl Read, stop: &AtomicBool) -> io::Result<(Reply,Vec<u8>,usize,u64,u64,u64)> {
    let (n,first,_)=length(input,MAX_JSON,stop)?; let mut head=vec![0;n]; exact(input,&mut head,stop)?;
    let t=std::time::Instant::now();
    let reply:Reply=serde_json::from_slice(&head).map_err(io::Error::other)?;
    let decode_ns=crate::shared::ns(t.elapsed());
    let (p,_,_)=length(input,MAX_PROOF,stop)?;
    if p != reply.encoded_bytes { return Err(io::Error::other("reply body length mismatch")); }
    let mut bytes=vec![0;p]; let (_,end)=exact(input,&mut bytes,stop)?; Ok((reply,bytes,n+p+8,first,end,decode_ns))
}
