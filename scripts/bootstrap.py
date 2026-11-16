#!/usr/bin/env python3
"""Materialize the locked upstream sources and register every final proof target."""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
from release_common import (ROOT, ENGINE, RECORDS, LOCK, TOOLCHAIN, run,
                            source_repo, ensure_toolchain, export, copy_bridge)


def cached_transport(name, source_cache):
    if source_cache is None:
        return None
    for candidate in (source_cache / 'external' / name,
                      source_cache / 'external/eth-work/.lake/packages' / name,
                      source_cache / '.cache/git' / name):
        if (candidate / '.git').exists():
            return candidate
    return None


def checkout(pin, destination, source_cache):
    if not (destination / '.git').exists():
        if destination.exists() and any(destination.iterdir()):
            raise RuntimeError('Refusing to overwrite a non-Git directory: ' + str(destination))
        destination.mkdir(parents=True, exist_ok=True)
        run(['git', 'init', '--quiet', destination])
        run(['git', '-C', destination, 'remote', 'add', 'origin', pin['url']])
    present = subprocess.run(['git', '-C', str(destination), 'cat-file', '-e',
                              pin['rev'] + '^{commit}'], stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL).returncode == 0
    if not present:
        transport = cached_transport(pin['name'], source_cache) or pin['url']
        run(['git', '-C', destination, 'fetch', '--quiet', '--depth=1', transport, pin['rev']])
    dirty = subprocess.run(['git', '-C', str(destination), 'diff', '--quiet', 'HEAD', '--'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    head = subprocess.run(['git', '-C', str(destination), 'rev-parse', '--verify', 'HEAD'],
                          capture_output=True, text=True)
    if head.returncode == 0 and dirty.returncode != 0:
        raise RuntimeError('Refusing to replace edited dependency sources: ' + str(destination))
    if head.returncode == 0 and head.stdout.strip() != pin['rev']:
        raise RuntimeError('Dependency is at a different revision: ' + str(destination))
    if head.returncode != 0:
        run(['git', '-C', destination, 'checkout', '--quiet', '--detach', pin['rev']])


def prepare(source_cache=None, cache=False):
    for command in ('git', 'cc'):
        if not shutil.which(command):
            raise SystemExit('Missing prerequisite: ' + command)
    RECORDS.mkdir(parents=True, exist_ok=True)
    lean_version = ensure_toolchain()
    for pin in LOCK['sources']:
        repo = source_repo(pin['name'])
        checkout(pin, repo, source_cache)
        extracted = ROOT / 'external' / pin['name']
        stamp = extracted / '.release-source.json'
        if not extracted.exists():
            export(repo, pin['rev'], extracted)
            stamp.write_text(json.dumps(pin, indent=2) + '\n')
        elif not stamp.is_file() or json.loads(stamp.read_text()) != pin:
            raise RuntimeError('Unrecognized extracted source directory: ' + str(extracted))
    if not ENGINE.exists():
        shutil.copytree(ROOT / 'external/anthropic-formal-math/eth', ENGINE,
                        ignore=shutil.ignore_patterns('.git', '.lake'))
    copy_bridge(ROOT / 'external/eth-hamiltonicity', ENGINE / 'bridge')
    shutil.copy2(ROOT / 'config/engine.lakefile.toml', ENGINE / 'lakefile.toml')
    (ENGINE / 'lean-toolchain').write_text(LOCK['toolchain'] + '\n')
    (ENGINE / 'lake-manifest.json').write_text(json.dumps(LOCK['lake_manifest'], indent=2) + '\n')
    for package in LOCK['lake_manifest']['packages']:
        # A real Git checkout lets Lake verify the exact manifest revision.
        checkout(package, ENGINE / '.lake/packages' / package['name'], source_cache)
    if cache:
        run([TOOLCHAIN / 'bin/lake', 'exe', 'cache', 'get'], cwd=ENGINE)
    (RECORDS / 'bootstrap.json').write_text(json.dumps({
        'status': 'ready', 'toolchain': lean_version, 'sources': LOCK['sources'],
        'mathlib_revision': LOCK['lake_manifest']['packages'][0]['rev'],
        'mathlib_cache_requested': cache,
        'source_transport': 'local pinned Git objects' if source_cache else 'upstream Git URLs',
        'independent_specifications_registered': True,
    }, indent=2) + '\n')
    print('Ready: ./scripts/unified_lake build PrimeIndependent.Solution', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache', action='store_true', help='Download the pinned Mathlib proof cache (ordinary build only)')
    parser.add_argument('--source-cache', type=Path, help='Optional existing checkout supplying pinned Git objects; never copies proof artifacts')
    args = parser.parse_args()
    prepare(args.source_cache.resolve() if args.source_cache else None, args.cache)

