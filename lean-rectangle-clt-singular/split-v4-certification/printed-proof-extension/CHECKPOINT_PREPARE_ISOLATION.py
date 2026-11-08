#!/usr/bin/env python3
"""Prepare, but do not execute, the frozen printed-proof checkpoint."""
import argparse, hashlib, json, os, pathlib, shlex, subprocess
P = pathlib.Path
PKGS = ('lean-kane', 'lean-rectangle-clt-local', 'lean-rectangle-clt-singular')
def git(root, *args): return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 a=argparse.ArgumentParser();a.add_argument('--commit',required=True);a.add_argument('--source-root',type=P,default=P('/workspace/HDCLTs-printed-proofs'));a.add_argument('--worktree',type=P);a.add_argument('--logs',type=P);args=a.parse_args()
 root=args.source_root.resolve();commit=git(root,'rev-parse',args.commit+'^{commit}')
 assert len(commit)==40 and all(c in '0123456789abcdef' for c in commit)
 assert git(root,'rev-parse','HEAD')==commit,'Source cache checkout must be the frozen commit.'
 work=(args.worktree or P('/workspace')/('HDCLTs-printed-checkpoint-'+commit[:7])).resolve()
 cert=root/'lean-rectangle-clt-singular/split-v4-certification'
 logs=(args.logs or cert/('logs-printed-checkpoint-'+commit[:7])).resolve()
 assert not work.exists(),f'Refusing existing worktree {work}'
 assert not logs.exists(),f'Refusing existing evidence {logs}'
 common=(root/'lean-rectangle-clt-singular/.lake/packages').resolve()
 assert common.is_dir()
 oldfiles={str(p.relative_to(root)):sha(p) for p in cert.rglob('*') if p.is_file() and 'printed-proof-extension' not in p.relative_to(cert).parts}
 for name in ('VERIFICATION.json','SUBEXPONENTIAL_VERIFICATION.json','LOWER_RESULTS_VERIFICATION.json','SPLIT_V4_VERIFICATION.json'):
  p=root/'lean-rectangle-clt-singular'/name
  if p.is_file():oldfiles[str(p.relative_to(root))]=sha(p)
 subprocess.run(['git','worktree','add','--detach',str(work),commit],cwd=root,check=True)
 copied={}
 for name in PKGS:
  src=root/name/'.lake';dst=work/name/'.lake';dst.mkdir(parents=True,exist_ok=True)
  for item in sorted(src.iterdir()):
   if item.name=='packages':continue
   assert not item.is_symlink(),f'Unexpected shared project cache: {item}'
   subprocess.run(['cp','-a','--reflink=auto',str(item),str(dst/item.name)],check=True)
  (dst/'packages').symlink_to(common,target_is_directory=True)
  regular=0
  for path in (dst/'build').rglob('*'):
   if path.is_symlink():
    assert path.resolve().is_relative_to(work),f'Project build symlink escapes isolation: {path}'
   elif path.is_file():
    origin=src/path.relative_to(dst)
    assert (path.stat().st_dev,path.stat().st_ino)!=(origin.stat().st_dev,origin.stat().st_ino),f'Hard-linked project file: {path}'
    regular+=1
  copied[name]={'source_lake':str(src),'destination_lake':str(dst),'independent_regular_build_files':regular,'shared_third_party_packages':str(common)}
 env=os.environ.copy();env['ELAN_HOME']='/workspace/.elan';env['PATH']='/workspace/.elan/bin:'+env.get('PATH','');env['MATHLIB_CACHE_DIR']='/workspace/.cache/mathlib'
 pkg=work/'lean-rectangle-clt-singular'
 plan=subprocess.check_output(['python3','split-v4-certification/run.py','checkpoint','--skip-cache','--plan'],cwd=pkg,env=env,text=True)
 assert 'PrintedDependencyAudit [axiom_audit]' in plan
 assert 'PrintedCorrespondenceAudit [axiom_audit]' in plan
 assert 'PrintedRouteAudit [axiom_audit]' in plan
 runnerlog=logs.parent/'runner.log'
 logs.parent.mkdir(parents=True,exist_ok=True)
 command=['python3','split-v4-certification/run.py','checkpoint','--skip-cache','--stream','--output',str(logs)]
 preflight={'proof_commit':commit,'source_cache_checkout':str(root),'isolated_worktree':str(work),'logs':str(logs),'runner_stdout':str(runnerlog),'command':command,'cwd':str(pkg),'command_count':len(plan.splitlines()),'pinned_environment':{k:env[k] for k in ('ELAN_HOME','MATHLIB_CACHE_DIR')},'project_caches':copied,'preserved_old_files_sha256':oldfiles,'planned_commands':plan.splitlines()}
 output=P('/tmp')/('printed-isolation-'+commit[:7]+'.json');output.write_text(json.dumps(preflight,indent=2)+'\n')
 print(json.dumps({'preflight':str(output),'commit':commit,'worktree':str(work),'logs':str(logs),'command_count':len(plan.splitlines()),'runner_stdout':str(runnerlog),'command':shlex.join(command)},indent=2))
 print('Prepared only: final checkpoint has NOT been started.')
if __name__=='__main__':main()
