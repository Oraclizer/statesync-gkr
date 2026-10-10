"""Linux build and bounded real controls in a fresh temporary workspace."""
import argparse,hashlib,json,os,platform,shutil,socket,subprocess,sys,tarfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
IMMUTABLE='1b8d2f829792172b347dedbfde969016c2c05789'
def require(ok,message):
    if not ok:raise ValueError(message)
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def rows(path):
    with path.open(encoding='utf-8') as file:
        return [json.loads(line) for line in file if line.strip()]
def invoke(command,env,log,timeout=600):
    with log.open('xb') as output:subprocess.run([str(x) for x in command],env=env,stdout=output,stderr=subprocess.STDOUT,check=True,timeout=timeout)
def prepare_memory_source(repo,revision,work,env):
    # Use the checked current BSL source. The installer still enforces the
    # exact historical reduction bytes before appending its test-only child.
    archive=work/'current-bsl-source.tar'
    with archive.open('xb') as f:subprocess.run(['git','-c','safe.directory='+str(repo),'-C',str(repo),'archive','--format=tar',revision],stdout=f,check=True)
    source=work/'MemorySource';source.mkdir()
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            p=Path(member.name);require(not p.is_absolute() and '..' not in p.parts and (member.isfile() or member.isdir()),'unsafe source archive member')
        tar.extractall(source,filter='data')
    memory=work/'Memory';shutil.copytree(ROOT/'Memory',memory)
    invoke([sys.executable,memory/'install-probe.py','--source',source,'--receipt',memory/'install-receipt.json'],env,work/'memory-install.log',timeout=20)
    shutil.copyfile(memory/'Cargo.lock',source/'Cargo.lock')
    return source,memory

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    require(sys.platform.startswith('linux'),'Linux runner required');require(not args.out.exists(),'fresh output root required')
    work=args.out.resolve();work.mkdir(parents=True);repo=ROOT.parents[1]
    def git(*xs):return subprocess.check_output(['git','-c','safe.directory='+str(repo),'-C',str(repo),*xs],text=True).strip()
    require(not git('status','--porcelain'),'clean current source required')
    current=git('rev-parse','HEAD');env=os.environ.copy();env['CARGO_TARGET_DIR']=str(work/'Target')
    invoke([sys.executable,repo/'release/v1.1/verify.py','--mode','clean-history'],env,work/'source-consistency.log',timeout=60)
    # Caller dependency path refers to the unchanged checkout root. Only its
    # standalone benchmark crate is built; production source is not edited.
    invoke(['cargo','build','--release','--locked','--manifest-path',ROOT/'Load/Cargo.toml'],env,work/'load-build.log')
    binary=work/'Target/release/ssgkr-load-driver';require(binary.is_file(),'compiled caller absent')
    invoke([sys.executable,ROOT/'smoke.py','--binary',binary,'--out',work/'LoadControls'],env,work/'load-controls.log',timeout=60)
    negatives={}
    for name,flags,message in [('unknown-flag',['--not-a-supported-flag','1'],'unsupported option'),('duplicate-flag',['--workers','1','--workers','2'],'duplicate option')]:
        result=subprocess.run([str(binary),'controls',*flags],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=15)
        (work/(name+'.log')).write_text(result.stdout,encoding='utf-8')
        require(result.returncode!=0 and message in result.stdout,'CLI negative control falsely succeeded');negatives[name]={'exit':result.returncode,'rejected':True}
    # Loopback is a local functional check, with no throughput claim. Pick an
    # available local port; read readiness from the real server log.
    with socket.socket() as s:s.bind(('127.0.0.1',0));port=s.getsockname()[1]
    endpoint=f'127.0.0.1:{port}';serverout=work/'Server';frontout=work/'Frontend'
    env.update(SSGR_SOURCE_SHA=current,SSGR_DRIVER_SHA=json.loads((work/'LoadControls/small-check-receipt.json').read_text())['actual_portable_driver_sha256'],SSGR_BINARY_SHA=sha(binary),SSGR_ENVIRONMENT_SHA=hashlib.sha256(json.dumps({'platform':platform.platform(),'cpus':os.cpu_count(),'scope':'local smoke'},sort_keys=True).encode()).hexdigest(),SSGR_HARDWARE_PROFILE='loopback-small-controls')
    serverlog=(work/'server-console.log').open('xb')
    server=subprocess.Popen([str(binary),'server','--out',str(serverout),'--host-id','local-server','--run-id','localhost-small','--depth','8','--workers','2','--batch-max','3','--max-wait-us','1000','--run-ms','5000','--control-samples','2','--listen',endpoint,'--telemetry-ms','20','--log-flush-every','1'],env=env,stdout=serverlog,stderr=subprocess.STDOUT)
    try:
        ready=False;until=time.monotonic()+30
        while time.monotonic()<until:
            require(server.poll() is None,'server exited before readiness')
            if (serverout/'server.jsonl').exists():
                try:ready=any(r.get('event')=='ready' for r in rows(serverout/'server.jsonl'))
                except json.JSONDecodeError:ready=False
            if ready:break
            time.sleep(.02)
        require(ready,'server readiness timed out')
        invoke([binary,'load','--out',frontout,'--host-id','local-frontend','--run-id','localhost-small','--depth','8','--verify-workers','2','--corpus','2','--control-samples','2','--targets',endpoint,'--rate','10','--jobs','6','--warmup-jobs','3','--deadline-ms','10000','--drain-ms','15000','--telemetry-ms','20'],env,work/'frontend-console.log',timeout=40)
        require(server.wait(timeout=15)==0,'server process failed')
    finally:
        if server.poll() is None:server.terminate();server.wait(timeout=10)
        serverlog.close()
    front=rows(frontout/'frontend.jsonl');back=rows(serverout/'server.jsonl')
    offered={r['job_id']:r for r in front if r.get('event')=='offered'};accepted={r['job_id']:r for r in front if r.get('event')=='completed'}
    arrived={r['job_id']:r for r in back if r.get('event')=='server_arrival'};returned={r['reply']['job_id']:r for r in back if r.get('event')=='server_return'}
    for stream,event in [(front,'offered'),(front,'completed'),(back,'server_arrival'),(back,'server_return')]:require(sum(r.get('event')==event for r in stream)==9,'duplicate/missing localhost event')
    expected=set(range(9));require(set(offered)==set(accepted)==set(arrived)==set(returned)==expected,'localhost request-chain loss/duplicate')
    require(sum(r['warmup'] is True for r in offered.values())==3,'warmup count drift')
    for i in expected:
        x=accepted[i];require(x.get('accepted') is True and x.get('reply_binding') is True and x.get('reply_hash_matches') is True and x.get('control_reference_hash_matches') is True,'encoded original-request acceptance failed')
        require(offered[i]['input_sha256']==arrived[i]['input_sha256'],'server input binding mismatch')
        require(x['canonical_sha256']==returned[i]['reply']['canonical_sha256'] and x['encoded_bytes']==returned[i]['reply']['encoded_bytes'],'proof hash/length binding mismatch')
    forbidden=['generator_failure','send_error','drain_failure','protocol_error','input_error','server_reject','reader_failure']
    require(not any(r.get('event') in forbidden for r in front+back),'actual job failure in local smoke')
    source,memory=prepare_memory_source(repo,current,work,env)
    env.update(SSGKR_SOURCE_SHA=current,SSGKR_MEMORY_PROBE_SHA=sha(memory/'memory_probe.rs'),SSGKR_MEMORY_FAMILY='mixed',SSGKR_MEMORY_WIDTH_BITS='2',SSGKR_MEMORY_DEPTH='2',SSGKR_MEMORY_SAMPLES='1',SSGKR_MEMORY_WARMUPS='0',SSGKR_MEMORY_OBSERVER='1',SSGKR_MEMORY_REPEAT='1',SSGKR_MEMORY_SEED='7')
    test=['cargo','test','--release','--locked','--manifest-path',source/'Cargo.toml','-p','ssgkr-protocol']
    invoke(test+['memory_probe_controls','--','--nocapture','--test-threads=1'],env,work/'memory-controls.log')
    raw=[]
    for mode in ['dense','sparse']:
        output=work/(mode+'-tiny.jsonl');raw.append(output);modeenv=env.copy();modeenv.update(SSGKR_MEMORY_MODE=mode,SSGKR_MEMORY_OUT=str(output))
        invoke(test+['memory_probe_one','--','--ignored','--nocapture','--test-threads=1'],modeenv,work/(mode+'-tiny.log'))
    invoke([sys.executable,memory/'verify-raw.py','--raw',*raw,'--controls-log',work/'memory-controls.log'],env,work/'memory-verify.log',timeout=30)
    receipt={'schema':'ssgkr.public-linux-small-smoke.v1','status':'PASS','actual_source_commit':current,'actual_memory_source_commit':current,'historical_memory_kernel_commit':IMMUTABLE,'memory_source_scope':'current-BSL-source-with-unchanged-historical-kernel','actual_load_binary_sha256':sha(binary),'cli_negatives':negatives,'local_timed_jobs':6,'local_warmup_jobs':3,'all_local_request_input_proof_bindings':True,'memory_cells':2,'memory_family':'mixed','memory_width':4,'memory_depth':2,'memory_timed_samples_per_cell':1,'memory_warmups_per_cell':0,'memory_controls_families':['mixed','add','mul','cubic_affine'],'memory_same_internal_proof':True,'source_production_mutations':0,'performance_claim':False,'raw_preserved_in_fresh_output':True}
    (work/'linux-small-smoke-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
