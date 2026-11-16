#!/usr/bin/env python3
"""Build all three independent endpoints using source-built dependencies, without caches."""
import datetime
import json
import shutil
import subprocess
import sys
import uuid
from independent_context import ROOT,RESEARCH,ENDPOINTS,context

UPSTREAM_TARGETS=['statements','machines','networks','threesat','consequences','sparsification','rates','variables','maintheorem','MainResults','Challenge','Solution','PaperIndex']
TARGETS=['Mathlib',*UPSTREAM_TARGETS,'PrimeIndependent.Solution','PrimeIndependent.Challenge','PrimeAlgorithm.PrimeFindingMachine']
COMMAND=[sys.executable,str(ROOT/'scripts/independent_lake.py'),'build',*TARGETS]


def main():
    prep,work,_,_=context()
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    had_dependencies=(work/'dependencies/mathlib/.lake/build/lib/lean/Mathlib.olean').is_file()
    data={'status':'running','started_utc':started,'workspace':str(work),
          'endpoints':ENDPOINTS,'validation_run_id':str(uuid.uuid4()),
          'targets':TARGETS,'reproduction_command':COMMAND,'actual_commands':[COMMAND],
          'initial_compiled_lean_artifacts':prep['initial_compiled_lean_artifacts'],
          'cache_policy':'--no-cache; system/artifact/Mathlib cache disabled; inherited Lean search paths removed',
          'bootstrap':prep['bootstrap'],'scope':prep['scope'],
          'log':str(RESEARCH/'independent-clean-build.log'),'per_file_hash_audit':False,
          'build_mode':('Incremental endpoint build using dependencies previously built from source'
                        if prep.get('full_source_build_record') else 'Full source build from the prepared zero-artifact workspace'),
          'local_dependency_outputs_present_before_build':had_dependencies,
          'full_source_build_record':prep.get('full_source_build_record')}
    report=RESEARCH/'independent-clean-build.json'
    report.write_text(json.dumps(data,indent=2)+'\n')
    with (RESEARCH/'independent-clean-build.log').open('w') as out:
        result=subprocess.run(COMMAND,stdout=out,stderr=subprocess.STDOUT)
    mathlib=work/'dependencies/mathlib'
    sources=list((mathlib/'Mathlib').rglob('*.lean'))+[mathlib/'Mathlib.lean']
    missing=[str(p.relative_to(mathlib)) for p in sources
             if not (mathlib/'.lake/build/lib/lean'/p.relative_to(mathlib).with_suffix('.olean')).is_file()]
    passed=result.returncode==0 and not missing
    data.update(status='passed' if passed else 'failed',exit_code=result.returncode,
                finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                mathlib_source_modules=len(sources),mathlib_modules_without_built_olean=missing)
    report.write_text(json.dumps(data,indent=2)+'\n')
    if passed and not prep.get('full_source_build_record'):
        archive=RESEARCH/'independent-history'/('source-build-'+data['validation_run_id'])
        archive.mkdir(parents=True)
        shutil.copy2(report,archive/report.name)
        shutil.copy2(RESEARCH/'independent-clean-build.log',archive/'independent-clean-build.log')
        prep['full_source_build_record']=str((archive/report.name).relative_to(ROOT))
        (RESEARCH/'independent-preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
    print('Three-endpoint source build '+data['status'])
    raise SystemExit(0 if passed else 1)
if __name__=='__main__':main()
