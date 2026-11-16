#!/usr/bin/env python3
"""Replay the complete import closure of all three proved endpoints in a fresh Lean kernel."""
from pathlib import Path
import datetime
import json
import subprocess
import sys
from independent_context import ENDPOINTS,context,completed_build

ROOT=Path(__file__).resolve().parents[1]
def main():
    _,work,_,_=context()
    build=completed_build(work)
    command=[sys.executable,str(ROOT/'scripts/independent_lake.py'),'env','leanchecker',
             '--fresh','--verbose','PrimeIndependent.Solution']
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    logfile=ROOT/'verification/local/independent-fresh-replay.log'
    report=ROOT/'verification/local/independent-fresh-replay.json'
    data={'status':'running','started_utc':started,'command':command,
          'workspace':str(work),'endpoints':ENDPOINTS,'validation_run_id':build['validation_run_id'],
          'scope':'All declarations of PrimeIndependent.Solution and its imports, including all three endpoints',
          'checker':'Pinned Lean 4.33.1 leanchecker --fresh; additional verification to nanoda',
          'log':str(logfile)}
    report.write_text(json.dumps(data,indent=2)+'\n')
    with logfile.open('w') as out:
        result=subprocess.run(command,stdout=out,stderr=subprocess.STDOUT)
    data.update(status='passed' if result.returncode==0 else 'failed',exit_code=result.returncode,
                finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    report.write_text(json.dumps(data,indent=2)+'\n')
    print('Fresh replay '+data['status'])
    raise SystemExit(result.returncode)
if __name__=='__main__':main()
