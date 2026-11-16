#!/usr/bin/env python3
"""Build the final targets and check their recursive axiom dependencies."""
import datetime
import json
import re
import subprocess
from release_common import ROOT, ENGINE, RECORDS, environment

ENDPOINTS = ['PrimeIndependent.primeSum_time', 'PrimeIndependent.primeCounting_time',
             'PrimeIndependent.primeFinding_time']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    # Catch missing release files before starting the expensive engine build.
    module_roots = {'PrimeAlgorithm': ROOT / 'formal/unified',
                    'PrimeIndependent': ROOT / 'formal/independent',
                    'EthFollowup': ENGINE / 'bridge'}
    for source in (ROOT / 'formal').rglob('*.lean'):
        for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', source.read_text(), re.M):
            for module in line.split('--')[0].split():
                base = module_roots.get(module.split('.')[0])
                if base is not None and not (base.joinpath(*module.split('.')).with_suffix('.lean')).is_file():
                    raise SystemExit('Missing source for ' + module + '; run bootstrap and check the release files.')
    RECORDS.mkdir(parents=True, exist_ok=True)
    report = {'status': 'running', 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'scope': 'Final release targets; ordinary build and recursive axiom audit',
              'endpoints': ENDPOINTS}
    path = RECORDS / 'build-audit.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    commands = [
        [str(ROOT / 'scripts/unified_lake'), 'build', 'PrimeIndependent.Solution', 'PrimeIndependent.Challenge'],
        [str(ROOT / 'scripts/unified_lake'), 'env', 'lean', str(ROOT / 'formal/independent/PrintAxioms.lean')]]
    outputs = []
    for command, name in zip(commands, ['build.log', 'axioms.log']):
        with (RECORDS / name).open('w') as out:
            result = subprocess.run(command, cwd=ROOT, env=environment(), stdout=out, stderr=subprocess.STDOUT)
        outputs.append((RECORDS / name).read_text())
        if result.returncode:
            report.update(status='failed', exit_code=result.returncode, failed_log=name)
            path.write_text(json.dumps(report, indent=2) + '\n')
            raise SystemExit('Verification failed; see verification/local/' + name)
    axioms = {name: [a.strip() for a in values.split(',') if a.strip()]
              for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", outputs[-1])}
    passed = set(axioms) == set(ENDPOINTS) and all(set(a) <= ALLOWED for a in axioms.values())
    report.update(status='passed' if passed else 'failed', axioms=axioms, exit_code=0 if passed else 1,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    path.write_text(json.dumps(report, indent=2) + '\n')
    print('Three final endpoints: ' + report['status'])
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()

