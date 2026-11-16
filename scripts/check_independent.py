#!/usr/bin/env python3
"""Compare the Mathlib-only endpoints and replay the exported proofs in two kernels.

Run after prepare_independent.py and the source-only build. No source digest
sweeps are used: acceptance requires Comparator and both actual kernels.
"""
from pathlib import Path
import datetime
import json
import os
import platform
import subprocess
import sys
from independent_context import ENDPOINTS,context,completed_build

ROOT=Path(__file__).resolve().parents[1]
RESEARCH=ROOT/'verification/local'

def main():
    _,work,cfg,settings=context()
    build=completed_build(work)
    comparator=ROOT/'external/verification-tools/comparator/.lake/build/bin/comparator'
    exporter=ROOT/'external/verification-tools/lean4export/.lake/build/bin/lean4export'
    nanoda=ROOT/'.elan/toolchains/leanprover--lean4---v4.35.0/bin/nanoda_bin'
    sandbox=ROOT/'scripts/comparator_macos_sandbox.py'
    if platform.system()!='Darwin':
        raise SystemExit('This configured runner uses macOS Seatbelt; use upstream Landrun on Linux')
    for path in (comparator,exporter,nanoda,sandbox):
        if not os.access(path,os.X_OK): raise SystemExit('Missing executable: '+str(path))
    env=os.environ.copy()
    env.update({'COMPARATOR_LANDRUN':str(sandbox),'COMPARATOR_LEAN4EXPORT':str(exporter),
                'COMPARATOR_NANODA':str(nanoda),'LEAN_ABORT_ON_PANIC':'1'})
    command=[sys.executable,str(ROOT/'scripts/independent_lake.py'),'env',str(comparator),str(cfg)]
    pathcheck=subprocess.check_output([sys.executable,str(ROOT/'scripts/independent_lake.py'),
                                      'env','/usr/bin/printenv','LEAN_PATH'],env=env,text=True).strip()
    search_paths=[Path(p).resolve() for p in pathcheck.split(':') if p]
    bootstrap=(ROOT/'.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean').resolve()
    if not search_paths or any(work not in p.parents and p!=work and p!=bootstrap for p in search_paths):
        raise SystemExit('LEAN_PATH escapes the isolated source build: '+pathcheck)
    log=RESEARCH/'independent-comparator.log'
    report=RESEARCH/'independent-comparator.json'
    data={'status':'running','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'workspace':str(work),'configuration':str(cfg),
          'endpoints':ENDPOINTS,'validation_run_id':build['validation_run_id'],
          'theorems':settings['theorem_names'],'permitted_axioms':settings['permitted_axioms'],
          'lean_path':pathcheck,'bootstrap_library':str(bootstrap),'sandbox':'macOS Seatbelt adapter; default-deny writes and network',
          'comparator':'leanprover/comparator @ 575674928e239f5bc452aab72d1dd7b0f1326494',
          'exporter':'lean4export v4.33.0 built with Lean v4.33.1',
          'nanoda':'nanoda_bin 0.4.19 from the official Lean v4.35.0 toolchain',
          'log':str(log),'command':command}
    report.write_text(json.dumps(data,indent=2)+'\n')
    with log.open('w') as output:
        result=subprocess.run(command,env=env,stdout=output,stderr=subprocess.STDOUT)
    content=log.read_text()
    checks={'comparator_acceptance':'Your solution is okay!' in content,
            'nanoda_acceptance':'nanoda kernel accepts the solution' in content,
            'lean_replay_acceptance':'Lean default kernel accepts the solution' in content}
    success=result.returncode==0 and all(checks.values())
    data.update({'status':'passed' if success else 'failed','exit_code':result.returncode,
                 'checks':checks,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
    report.write_text(json.dumps(data,indent=2)+'\n')
    print(('PASS' if success else 'FAIL')+': independent S(N), pi(N), and prime-finding endpoints; '+str(log))
    raise SystemExit(0 if success else 1)

if __name__=='__main__': main()
