#!/usr/bin/env python3
"""Summarize one complete three-endpoint verification run, without file hashes."""
import datetime
import json
from independent_context import ROOT,RESEARCH,ENDPOINTS,context,inputs_precede_build


def main():
    prep,work,_,_=context()
    records={key:json.loads((RESEARCH/name).read_text()) for key,name in {
      'preparation':'independent-preparation.json','source_build':'independent-clean-build.json',
      'fresh_replay':'independent-fresh-replay.json','independent_kernel':'independent-comparator.json',
      'tools':'independent-tools.json'}.items()}
    stages=['source_build','fresh_replay','independent_kernel']
    build=records['source_build'];run_id=build.get('validation_run_id')
    baseline_path=build.get('full_source_build_record')
    baseline_file=ROOT/baseline_path if baseline_path else RESEARCH/'independent-clean-build.json'
    baseline=json.loads(baseline_file.read_text())
    baseline_log=baseline_file.with_suffix('.log')
    records['full_source_build_baseline']=baseline
    checks={
      'zero_artifact_start':prep['initial_compiled_lean_artifacts']==0,
      'full_source_build_baseline':(
          (bool(baseline_path) or build.get('build_mode')=='Full source build from the prepared zero-artifact workspace')
          and baseline.get('status')=='passed' and baseline.get('exit_code')==0
          and baseline.get('initial_compiled_lean_artifacts')==0
          and baseline.get('workspace')==str(work)
          and baseline.get('mathlib_modules_without_built_olean')==[]
          and baseline.get('mathlib_source_modules',0)>0
          and baseline.get('mathlib_source_modules')==build.get('mathlib_source_modules')
          and bool(baseline.get('finished_utc'))
          and all(k in baseline.get('targets',[]) for k in ['Mathlib','PrimeAlgorithm.PrimeFindingMachine'])
          and (not baseline_path or baseline.get('finished_utc','')<=build['started_utc'])
          and baseline_log.is_file()),
      'all_stages_passed':all(records[k].get('status')=='passed' and records[k].get('exit_code')==0 for k in stages),
      'all_three_endpoints':all(records[k].get('endpoints')==ENDPOINTS for k in stages),
      'same_workspace':all(records[k].get('workspace')==str(work) for k in stages),
      'same_run':bool(run_id) and all(records[k].get('validation_run_id')==run_id for k in stages),
      'inputs_unchanged_since_build':inputs_precede_build(work,build),
      'checks_after_build':bool(build.get('finished_utc')) and all(
          records[k].get('started_utc','')>=build['finished_utc'] for k in stages[1:]),
      'kernel_acceptances':all(records['independent_kernel'].get('checks',{}).get(k) is True
          for k in ['comparator_acceptance','nanoda_acceptance','lean_replay_acceptance']),
      'tools_ready':records['tools']['status']=='ready'}
    good=all(checks.values())
    result={'status':'passed' if good else 'incomplete',
            'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'endpoints':ENDPOINTS,'validation_run_id':run_id,'coverage_checks':checks,
            'full_source_build_record':str(baseline_file),'full_source_build_log':str(baseline_log),
            'scope':prep['scope'],'bootstrap':prep['bootstrap'],
            'per_file_hash_audit':False,'records':records}
    (RESEARCH/'independent-chain.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Independent three-endpoint verification chain: '+result['status'])
    if not good:print('Unmet checks: '+', '.join(k for k,v in checks.items() if not v))
    raise SystemExit(0 if good else 1)
if __name__=='__main__':main()
