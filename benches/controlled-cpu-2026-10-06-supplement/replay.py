#!/usr/bin/env python3
"""Generic Linux replay. Default smoke is not the published 175-process study."""
import argparse,csv,hashlib,json,os,pathlib,shutil,subprocess,sys,urllib.request
from datetime import datetime,timezone

SOURCE_SHA='d22e2200378e21a40c254eab8df4d44dfea81f2806f02f0c9030636300d489e9'
SOURCE_URL='https://github.com/Oraclizer/statesync-gkr/releases/download/v1.1.0/statesync-gkr-v1.1-source.tar.gz'
BASE_SHA='b2d5a631e8527bca90d22065ca3692da48863f236f306d5217e8e4528fa1c75c'
UTC=lambda:datetime.now(timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,**options):subprocess.run(cmd,check=True,**options)

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--mode',choices=('smoke','full'),default='smoke')
 p.add_argument('--output',type=pathlib.Path,required=True)
 a=p.parse_args();artifact=pathlib.Path(__file__).resolve().parent;work=a.output.resolve()
 if sys.platform!='linux' or sys.version_info<(3,11):raise SystemExit('Linux and Python3.11+ required')
 if work.exists():raise SystemExit('Use a new output directory')
 for tool in ('cargo','rustc','taskset','lscpu','tar'):
  if not shutil.which(tool):raise SystemExit('Install prerequisite: '+tool)
 if not pathlib.Path('/usr/bin/time').is_file():raise SystemExit('GNU /usr/bin/time required')
 for name in ('CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_TARGET','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS'):
  if os.environ.get(name):raise SystemExit('Unset '+name+' for the fixed build profile')
 topology=subprocess.check_output(['lscpu','-p=CPU,CORE,SOCKET,NODE'],text=True)
 allowed=os.sched_getaffinity(0);cores={}
 for line in topology.splitlines():
  if line.startswith('#') or not line.strip():continue
  cpu,core,socket,node=map(int,line.split(','))
  if cpu in allowed:cores.setdefault((socket,core),cpu)
 cpus=','.join(str(c) for c in sorted(cores.values()))
 if not cpus:raise SystemExit('No allowed physical CPU set')
 mem=int(next(l.split()[1] for l in pathlib.Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemTotal:')))
 flags=pathlib.Path('/proc/cpuinfo').read_text()
 if a.mode=='full' and (len(cores)!=192 or len(allowed)!=192 or mem/1024/1024<360 or 'avx512f' not in flags):
  raise SystemExit('Full profile requires192 physical/logical CPUs and recorded384GiB host profile; 360GiB check is not engine minimum RAM')
 original=json.loads((artifact/'provenance.json').read_text())
 for item in original['driver_inputs']:
  if sha(artifact/item['path'])!=item['sha256']:raise SystemExit('Measured driver/lock mismatch')
 base=artifact.parent/'controlled-cpu-2026-10-06'
 if sha(base/'driver/src/main.rs')!=BASE_SHA:raise SystemExit('Original control caller pin mismatch')
 work.mkdir(parents=True);source=work/'source';source.mkdir()
 urllib.request.urlretrieve(SOURCE_URL,work/'source.tar.gz')
 if sha(work/'source.tar.gz')!=SOURCE_SHA:raise SystemExit('Immutable source archive mismatch')
 run(['tar','-xzf',str(work/'source.tar.gz'),'-C',str(source)])
 shutil.copytree(artifact/'driver',work/'driver')
 shutil.copytree(base/'driver',work/'baseline-driver')
 env=os.environ.copy();env.update(RUSTFLAGS='-Ctarget-cpu=native',CARGO_TARGET_DIR=str(work/'target-native'),CARGO_BUILD_JOBS='16',LC_ALL='C')
 for driver in ('driver','baseline-driver'):
  run(['cargo','+1.96.1','build','--release','--locked','--manifest-path',str(work/driver/'Cargo.toml')],env=env)
 import tomllib
 release=tomllib.loads((source/'Cargo.lock').read_text())['package']
 current=tomllib.loads((work/'driver/Cargo.lock').read_text())['package']
 byname={p['name']:(p['version'],p.get('source'),p.get('checksum')) for p in release}
 for item in current:
  if item['name'] in byname and (item['version'],item.get('source'),item.get('checksum'))!=byname[item['name']]:raise SystemExit('Common release dependency mismatch')
 controls=work/'OriginalControls';controls.mkdir()
 basebin=work/'target-native/release/ssgkr-benchmark-driver'
 for depth in (24,28,32):
  for kind in ('membership','nonmembership','update'):
   run(['taskset','-c',cpus,str(basebin),'--phase','controls','--kind',kind,'--depth',str(depth),'--workers','1','--samples','1','--batch','1','--mode','native','--run','0','--proof-dir',str(controls)],env=env,stdout=subprocess.DEVNULL)
 hashes={}
 for r in csv.DictReader((base/'control-hashes.csv').open()):hashes.setdefault((r['kind'],int(r['depth'])),[]).append(r['canonical_sha256'])
 for (kind,depth),values in hashes.items():
  if sha(controls/f'native-{kind}-d{depth}.bin')!=values[0]:raise SystemExit('Original representative proof mismatch')
  (controls/f'native-{kind}-d{depth}.hashes').write_text('\n'.join(values)+'\n')
 binary=work/'target-native/release/ssgkr-supplement-driver'
 tracked=[work/item['path'] for item in original['driver_inputs']]+[binary]
 before={str(x.relative_to(work)):sha(x) for x in tracked}
 source_before={str(x.relative_to(source)):sha(x) for x in source.rglob('*') if x.is_file()}
 plan=json.loads((artifact/'plan.json').read_text())
 if a.mode=='smoke':
  selected=[]
  selected.append(next(c for c in plan['cells'] if c['suite']=='A' and c['kind']=='membership' and c['depth']==24))
  selected.append(next(c for c in plan['cells'] if c['suite']=='B' and c['kind']=='membership' and c['batch']==32 and c['workers']==48))
  for variant in ('tombstone_nonmembership','empty_to_occupied','occupied_to_tombstone','tombstone_to_occupied','zero_payload_member','max_payload_member','root_chain_update','large_key_member'):
   selected.append(next(c for c in plan['cells'] if c['suite']=='C' and c['variant']==variant))
  plan['cells']=[dict(c,samples=1 if c['suite']=='B' else 3,warmup=1,repeat=1,order_index=i,cell_id=f'smoke-{i}-{c["suite"]}') for i,c in enumerate(selected)]
 plan['binary_sha256']=sha(binary)
 campaign=work/'campaign';campaign.mkdir()
 (campaign/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
 env.update(SSGR_SOURCE_SHA=SOURCE_SHA,SSGR_DRIVER_SHA=plan['driver_manifest_sha256'],SSGR_BINARY_SHA=plan['binary_sha256'],SSGR_CPUSET=cpus)
 run(['taskset','-c',cpus,str(binary),'--suite','representative','--out',str(work/'representative-controls'),'--baseline',str(controls)],env=env)
 for cell in plan['cells']:
  target=campaign/cell['cell_id'];target.mkdir();started=UTC()
  command=['/usr/bin/time','-v','-o',str(target/'process.time.txt'),'taskset','-c',cpus,str(binary)]
  for name in ('suite','kind','depth','batch','workers','samples','warmup','repeat','variant'):
   command.extend(['--'+name,str(cell[name])])
  command.extend(['--order',str(cell['order_index']),'--cell',cell['cell_id'],'--out',str(target),'--baseline',str(controls)])
  (target/'execution.json').write_text(json.dumps({'start_utc':started,'cell':cell})+'\n')
  with (target/'stdout.txt').open('w') as stdout,(target/'stderr.txt').open('w') as stderr:
   result=subprocess.run(command,env=env,stdout=stdout,stderr=stderr)
  (target/'exit.json').write_text(json.dumps({'exit_code':result.returncode,'finish_utc':UTC()})+'\n')
  if result.returncode:raise SystemExit('Measurement cell failed')
 for name,digest in before.items():
  if sha(work/name)!=digest:raise SystemExit('Driver/lock/native binary changed during replay')
 if {str(x.relative_to(source)):sha(x) for x in source.rglob('*') if x.is_file()}!=source_before:raise SystemExit('Released source changed during replay')
 terminal='supplement175-processes=PASS' if a.mode=='full' else 'supplement-schema-smoke=PASS'
 (campaign/'measurement-terminal.txt').write_text(terminal+'\n')
 if a.mode=='full':(campaign/'terminal.txt').write_text('supplement-full-campaign=PASS\n')
 run([sys.executable,str(artifact/'validate-cells.py'),str(campaign/'plan.json'),str(campaign),str(work/'validation.json')]+(['--smoke'] if a.mode=='smoke' else []))
 profile={'mode':a.mode,'status':'SMOKE_ONLY' if a.mode=='smoke' else 'OTHER_ENVIRONMENT_REPLAY','clock_tick_hz':os.sysconf('SC_CLK_TCK'),'physical_cpu_set':cpus,'driver_inputs_unchanged':True,'source_files_unchanged':True,'native_binary_sha256':sha(binary),'note':'Replayed on the caller host; metadata matching does not establish identical hardware or background load. Source/ABI/proof identity are not changed.'}
 (work/'replay-result.json').write_text(json.dumps(profile,indent=2)+'\n')
 print(json.dumps(profile))

if __name__=='__main__':main()
