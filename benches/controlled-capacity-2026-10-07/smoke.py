"""Run six small real controls using an already built caller; no build/download."""
import argparse,hashlib,json,os,platform,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def require(ok,message):
    if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--binary',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    require(not a.out.exists(),'fresh output directory required');require(a.binary.is_file(),'built caller absent')
    repo=ROOT.parents[1]
    source=subprocess.check_output(['git','-c','safe.directory='+str(repo),'-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    records=[{'path':p.relative_to(ROOT/'Load').as_posix(),'sha256':sha(p)} for p in sorted((ROOT/'Load').rglob('*')) if p.is_file() and ('src' in p.parts or p.name in ['Cargo.toml','Cargo.lock'])]
    driver=hashlib.sha256(json.dumps(records,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    environment={'platform':platform.platform(),'python':platform.python_version(),'logical_cpus':os.cpu_count(),'scope':'six small caller controls; not a throughput measurement'}
    env=os.environ.copy();env.update(SSGR_SOURCE_SHA=source,SSGR_DRIVER_SHA=driver,SSGR_BINARY_SHA=sha(a.binary),SSGR_ENVIRONMENT_SHA=hashlib.sha256(json.dumps(environment,sort_keys=True).encode()).hexdigest(),SSGR_HARDWARE_PROFILE='small-caller-controls')
    subprocess.run([str(a.binary.resolve()),'controls','--out',str(a.out.resolve()),'--host-id','local-control','--run-id','small-controls','--repeat','1','--depth','8','--workers','2','--control-samples','2'],env=env,check=True)
    rows=[json.loads(x) for x in (a.out/'controls.jsonl').read_text().splitlines()];controls=[r for r in rows if r.get('event')=='control']
    require(len(controls)==6 and {(r['kind'],r['fixture_id']) for r in controls}=={(k,i) for k in ['membership','nonmembership','update'] for i in [0,1]},'control family/corpus count mismatch')
    for r in controls:
        for key in ['positive','typed_proof_rejected','value_digest_rejected','old_root_rejected','trailing_bytes_rejected','sequential_parallel_proof_equal']:require(r.get(key) is True,'actual control failed or missing: '+key)
        payload=a.out/'controls'/f"{r['kind']}-{r['fixture_id']}.bin";require(payload.stat().st_size==r['encoded_bytes'] and sha(payload)==r['canonical_sha256'],'control payload hash/length mismatch')
    require(json.loads((a.out/'terminal.json').read_text())['status']=='CONTROLS_PASS','controls terminal absent')
    receipt={'schema':'ssgkr.small-caller-check.v1','status':'PASS','controls':len(controls),'actual_source_commit':source,'actual_portable_driver_sha256':driver,'actual_binary_sha256':sha(a.binary),'environment':environment,'performance_claim':False}
    (a.out/'small-check-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
