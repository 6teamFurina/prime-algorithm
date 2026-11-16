"""Shared endpoint and run checks for independent verification; no file hashes."""
from pathlib import Path
import datetime
import json

ROOT=Path(__file__).resolve().parents[1]
RESEARCH=ROOT/'verification/local'
ENDPOINTS=['PrimeIndependent.primeSum_time','PrimeIndependent.primeCounting_time',
           'PrimeIndependent.primeFinding_time']
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
INDEPENDENT_FILES=['PrimeIndependent/MainResults.lean','PrimeIndependent/Challenge.lean',
                   'PrimeIndependent/Solution.lean','PrintAxioms.lean','comparator.json']


def project_inputs(work):
    pairs=[(ROOT/'formal/independent'/p,work/'formal/independent'/p) for p in INDEPENDENT_FILES]
    pairs += [(p,work/'formal/unified'/p.relative_to(ROOT/'formal/unified'))
              for p in (ROOT/'formal/unified').rglob('*.lean')]
    pairs += [(p,work/'bridge'/p.relative_to(ROOT/'formal/bridge'))
              for p in (ROOT/'formal/bridge').rglob('*.lean')]
    return pairs


def context():
    prep=json.loads((RESEARCH/'independent-preparation.json').read_text())
    work=Path(prep['workspace']).resolve()
    config=work/'formal/independent/comparator.json'
    settings=json.loads(config.read_text())
    canonical=json.loads((ROOT/'formal/independent/comparator.json').read_text())
    if settings!=canonical:
        raise RuntimeError('Synchronize the independent source files and comparator configuration first')
    for source,copied in project_inputs(work):
        if source.read_bytes()!=copied.read_bytes():
            raise RuntimeError('Independent source is not synchronized: '+str(source.relative_to(ROOT)))
    expected=(ROOT/'config/engine.lakefile.toml').read_text().replace(
        '../../formal/unified','formal/unified').replace('../../formal/independent','formal/independent')
    if (work/'lakefile.toml').read_text()!=expected:
        raise RuntimeError('Independent Lake configuration differs from the release template')
    if settings.get('theorem_names')!=ENDPOINTS:
        raise RuntimeError('The independent configuration must contain all three expected endpoints')
    if (set(settings.get('permitted_axioms',[]))!=ALLOWED_AXIOMS
        or settings.get('enable_nanoda') is not True
        or settings.get('definition_names')!=[]
        or settings.get('challenge_module')!='PrimeIndependent.Challenge'
        or settings.get('solution_module')!='PrimeIndependent.Solution'):
        raise RuntimeError('Unexpected independent verification configuration')
    return prep,work,config,settings


def inputs_precede_build(work,build):
    """Reject edits to the packaged proof inputs after build start; no file hashes."""
    if not build.get('started_utc'):
        return False
    started=datetime.datetime.fromisoformat(build['started_utc']).timestamp()
    return all(p.stat().st_mtime<=started for pair in project_inputs(work) for p in pair)


def completed_build(work):
    build=json.loads((RESEARCH/'independent-clean-build.json').read_text())
    if (build.get('status')!='passed' or build.get('exit_code')!=0
        or build.get('endpoints')!=ENDPOINTS or build.get('workspace')!=str(work)
        or not build.get('validation_run_id')):
        raise RuntimeError('Build all three independent endpoints before running the checkers')
    if not inputs_precede_build(work,build):
        raise RuntimeError('Independent inputs changed after build start; rebuild before checking')
    return build
