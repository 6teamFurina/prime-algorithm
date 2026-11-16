"""Pinned, repository-local paths shared by the release commands."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ENGINE = ROOT / 'external/eth-work'
RECORDS = ROOT / 'verification/local'
LOCK = json.loads((ROOT / 'dependencies.lock.json').read_text())
VERSION = LOCK['toolchain'].split(':', 1)[1]
TOOLCHAIN = ROOT / '.elan/toolchains' / ('leanprover--lean4---' + VERSION)


def environment():
    env = os.environ.copy()
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN',
                'LAKE_HOME', 'LAKE_OVERRIDE_LEAN', 'LAKE_CONFIG', 'LAKE_PKG_URL_MAP'):
        env.pop(key, None)
    env['ELAN_HOME'] = str(ROOT / '.elan')
    env['PATH'] = str(TOOLCHAIN / 'bin') + os.pathsep + env.get('PATH', '')
    env['MATHLIB_CACHE_DIR'] = str(ROOT / '.cache/mathlib')
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    return env


def run(command, cwd=ROOT, **kwargs):
    return subprocess.run([str(x) for x in command], cwd=cwd,
                          env=environment(), check=True, **kwargs)


def ensure_toolchain():
    if not (TOOLCHAIN / 'bin/lean').is_file():
        local = ROOT / '.elan/bin/elan'
        elan = str(local) if local.is_file() else shutil.which('elan')
        if not elan:
            raise SystemExit('Install elan from https://lean-lang.org/install/ and rerun. '
                             'On macOS, also install the Xcode Command Line Tools.')
        run([elan, 'toolchain', 'install', LOCK['toolchain']])
    result = run([TOOLCHAIN / 'bin/lean', '--version'], capture_output=True, text=True)
    if VERSION.removeprefix('v') not in result.stdout:
        raise RuntimeError('The installed Lean does not match the locked toolchain')
    return result.stdout.strip()


def source_repo(name):
    return ROOT / '.cache/git' / name


def export(repo, revision, destination, subtree=None):
    destination.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryFile() as stream:
        command = ['git', '-C', repo, 'archive', revision]
        if subtree:
            command.append(subtree)
        run(command, stdout=stream)
        stream.seek(0)
        with tarfile.open(fileobj=stream) as archive:
            # These are archives of the explicitly locked upstream repositories.
            archive.extractall(destination)


def copy_bridge(source_root, destination):
    for module in LOCK['upstream_bridge_modules']:
        relative = Path(*module.split('.')).with_suffix('.lean')
        source = source_root / 'lean-bridge-anthropic/bridge' / relative
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target, follow_symlinks=True)
    shutil.copytree(ROOT / 'formal/bridge', destination, dirs_exist_ok=True)

