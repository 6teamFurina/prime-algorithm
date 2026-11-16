#!/usr/bin/env python3
"""Prepare a fresh source-only workspace from the release's locked Git revisions."""
from pathlib import Path
import argparse
import json
import shutil
from release_common import ROOT, ENGINE, RECORDS, LOCK, export, source_repo, copy_bridge


def prepare(work):
    if work.exists():
        raise SystemExit('Refusing to overwrite an existing workspace: ' + str(work))
    if not (ENGINE / 'lakefile.toml').is_file():
        raise SystemExit('Run python3 scripts/bootstrap.py first.')
    RECORDS.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True)
    pins = LOCK['sources']
    for pin in pins:
        export(source_repo(pin['name']), pin['rev'], work / '_source' / pin['name'])
    for p in (work / '_source/anthropic-formal-math/eth').iterdir():
        if p.is_dir():
            shutil.copytree(p, work / p.name)
        else:
            shutil.copy2(p, work / p.name)
    copy_bridge(work / '_source/eth-hamiltonicity', work / 'bridge')
    shutil.copytree(ROOT / 'formal/unified', work / 'formal/unified')
    shutil.copytree(ROOT / 'formal/independent', work / 'formal/independent')
    manifest = json.loads(json.dumps(LOCK['lake_manifest']))
    source_pins = [{'name': p['name'], 'revision': p['rev'], 'url': p['url']} for p in pins]
    packages = []
    for package in manifest['packages']:
        name, revision = package['name'], package['rev']
        export(ENGINE / '.lake/packages' / name, revision, work / 'dependencies' / name)
        source_pins.append({'name': name, 'revision': revision, 'url': package['url']})
        local = {key: package[key] for key in ['name', 'scope', 'inherited', 'configFile', 'manifestFile']}
        local.update(type='path', dir='dependencies/' + name)
        packages.append(local)
    manifest['packages'] = packages
    (work / 'lake-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    config = (ROOT / 'config/engine.lakefile.toml').read_text()
    config = config.replace('../../formal/unified', 'formal/unified').replace('../../formal/independent', 'formal/independent')
    (work / 'lakefile.toml').write_text(config)
    artifacts = [p for p in work.rglob('*') if p.is_file() and
                 p.name.endswith(('.olean', '.ilean', '.ltar', '.olean.private', '.olean.server'))]
    if artifacts:
        raise RuntimeError('Source-only preparation contains proof artifacts: ' + str(artifacts[:5]))
    report = {'status': 'prepared', 'workspace': str(work), 'toolchain': LOCK['toolchain'],
              'source_pins': source_pins, 'initial_compiled_lean_artifacts': 0,
              'hash_audits': False,
              'dependency_materialization': 'git archive at locked revisions; local path manifest',
              'bootstrap': 'Pinned Lean 4.33.1 binary distribution, including Init/Lean/Std/Lake',
              'scope': 'Fresh isolated directory on this host; dependency and project proofs rebuilt from source'}
    (RECORDS / 'independent-preparation.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Prepared source-only workspace: ' + str(work))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'external/independent')
    prepare(parser.parse_args().work_dir.resolve())

