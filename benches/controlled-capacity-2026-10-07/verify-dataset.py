"""Freeze and verify a public package against an externally pinned exact contract."""
import argparse,csv,gzip,hashlib,importlib.util,json,os,stat
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CONTRACT_SCHEMA='ssgkr.public-dataset-contract.v1'
MANIFEST_SCHEMA='ssgkr.public-dataset-manifest.v1'
def require(ok,message):
    if not ok:raise ValueError(message)
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()
def strict(text):
    def pairs(items):
        result={}
        for k,v in items:
            require(k not in result,'duplicate JSON key');result[k]=v
        return result
    def constant(value):raise ValueError('nonfinite JSON value')
    return json.loads(text,object_pairs_hook=pairs,parse_constant=constant)
def is_digest(value):return type(value) is str and len(value)==64 and all(c in '0123456789abcdef' for c in value)
def regular_member(root,path):
    current=root
    for part in Path(path).parts:
        current=current/part;info=current.lstat()
        require(not stat.S_ISLNK(info.st_mode) and not getattr(info,'st_file_attributes',0)&1024,'symlink/reparse member refused')
    require(stat.S_ISREG(info.st_mode),'regular member required')
    target=current.resolve();require(root.resolve() in target.parents,'member escaped package');return target
def disk_members(root):
    require(root.is_dir(),'package root missing')
    require(not root.is_symlink() and not getattr(root.lstat(),'st_file_attributes',0)&1024,'symlink/reparse package root')
    result=[];pending=[root]
    while pending:
        current=pending.pop()
        with os.scandir(current) as scan:
            for entry in scan:
                info=entry.stat(follow_symlinks=False)
                require(not stat.S_ISLNK(info.st_mode) and not getattr(info,'st_file_attributes',0)&1024,'symlink/reparse in package')
                p=Path(entry.path)
                if stat.S_ISDIR(info.st_mode):pending.append(p)
                else:require(stat.S_ISREG(info.st_mode),'nonregular package member');result.append(p.relative_to(root).as_posix())
    return sorted(result)
def members(entries,root,hash_files):
    require(type(entries) is list and len(entries)>0,'entries must be nonempty list')
    paths=[]
    for entry in entries:
        require(type(entry) is dict,'entry object required')
        require(set(entry)=={'path','bytes','sha256','rows','kind'},'entry fields mismatch')
        path=entry['path'];require(type(path) is str and path and ':' not in path and '\\' not in path and not Path(path).is_absolute() and '..' not in Path(path).parts,'safe member required')
        require(type(entry['bytes']) is int and entry['bytes']>=0,'exact byte count integer required')
        require(is_digest(entry['sha256']),'exact digest required')
        require(entry['rows'] is None or (type(entry['rows']) is int and entry['rows']>=0),'row count type mismatch')
        require(entry['kind'] in ['json','analysis-report','jsonl','csv','csv-gzip','text-observation','proof-payload','portable-source','figure','license','replay-document'],'known member kind required')
        if entry['kind'] in ['json','analysis-report']:require(entry['rows']==1 and type(entry['rows']) is int,'JSON document row count must be one')
        elif entry['kind'] in ['jsonl','csv','csv-gzip','text-observation']:require(type(entry['rows']) is int,'tabular/text row count required')
        else:require(entry['rows'] is None,'nontabular row count must be null')
        paths.append(path)
        if hash_files:
            target=regular_member(root,path)
            require(target.stat().st_size==entry['bytes'] and sha(target)==entry['sha256'],'size/hash mismatch')
            if entry['kind']=='jsonl':
                count=0
                with target.open(encoding='utf-8') as file:
                    for line in file:require(bool(line.strip()),'blank row');strict(line);count+=1
                require(count==entry['rows'],'row count mismatch')
            elif entry['kind'] in ['csv','csv-gzip']:
                opener=gzip.open if entry['kind']=='csv-gzip' else Path.open
                csv.field_size_limit(64*1024*1024)
                with opener(target,mode='rt',encoding='utf-8',newline='') as file:
                    reader=csv.reader(file);header=next(reader)
                    require(len(set(header))==len(header),'duplicate CSV header');count=0
                    for row in reader:require(len(row)==len(header),'CSV row width mismatch');count+=1
                require(count==entry['rows'],'CSV row count mismatch')
            elif entry['kind'] in ['json','analysis-report']:strict(target.read_text(encoding='utf-8'))
            elif entry['kind']=='text-observation':require(len(target.read_text(encoding='utf-8').splitlines())==entry['rows'],'text observation line count mismatch')
    require(len(paths)==len(set(paths)),'duplicate member path')
    require(paths==sorted(paths),'member paths must be sorted')
    return paths
def verify(contract,expected_contract_sha,manifest,public):
    require(is_digest(expected_contract_sha),'external contract digest required')
    require(sha(contract)==expected_contract_sha,'contract authority hash mismatch')
    c=strict(contract.read_text(encoding='utf-8'));m=strict(manifest.read_text(encoding='utf-8'))
    require(type(c) is dict and c.get('schema')==CONTRACT_SCHEMA,'contract schema mismatch')
    require(type(m) is dict and m.get('schema')==MANIFEST_SCHEMA,'manifest schema mismatch')
    require(set(c)=={'schema','coverage','selection_authority_sha256','expected_path_count','expected_paths','entries','normalization_contract'},'contract fields mismatch')
    require(c['coverage'] in ['selected-existing-records','full-declared-study-census'],'coverage not declared')
    require(is_digest(c['selection_authority_sha256']),'selection authority missing')
    require(type(c['normalization_contract']) is dict and set(c['normalization_contract'])=={'numeric_identity','protected_payload','wire_bytes','alias'} and all(type(v) is str and v for v in c['normalization_contract'].values()),'normalization contract fields missing/invalid')
    require(type(c['expected_path_count']) is int and c['expected_path_count']>0,'expected path count invalid')
    paths=members(c['entries'],public,False)
    require(type(c['expected_paths']) is list and c['expected_paths']==paths and c['expected_path_count']==len(paths),'contract expected set mismatch')
    require(set(m)=={'schema','contract_sha256','path_count','files'},'manifest fields mismatch')
    require(m['contract_sha256']==expected_contract_sha,'manifest contract binding mismatch')
    require(type(m['path_count']) is int and m['path_count']==len(paths),'manifest count mismatch')
    actual=members(m['files'],public,True)
    require(actual==paths and m['files']==c['entries'],'exact expected member set/content mismatch')
    on_disk=disk_members(public)
    require(on_disk==paths,'unmanifested/missing filesystem members')
    return {'schema':'ssgkr.public-contract-verification.v1','status':'CONTRACT_FILES_VERIFIED_NOT_PUBLISHED','coverage':c['coverage'],'contract_sha256':expected_contract_sha,'path_count':len(paths),'license_and_publication_authority':'separate final owner choice'}
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--contract',type=Path,required=True);parser.add_argument('--contract-sha256',required=True)
    parser.add_argument('--manifest',type=Path,required=True);parser.add_argument('--public',type=Path,required=True)
    args=parser.parse_args();print(json.dumps(verify(args.contract,args.contract_sha256,args.manifest,args.public),indent=2))
if __name__=='__main__':main()
