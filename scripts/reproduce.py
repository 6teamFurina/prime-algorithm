#!/usr/bin/env python3
"""Run the complete source build, fresh replay, and independent dual-kernel check."""
from pathlib import Path
import argparse
import platform
import subprocess
import sys
from release_common import ROOT


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'external/independent')
    parser.add_argument('--resume', action='store_true', help='Rebuild and recheck the workspace recorded in verification/local')
    args = parser.parse_args()
    if platform.system() != 'Darwin':
        raise SystemExit('The bundled dual-kernel runner uses macOS Seatbelt. '
                         'Ordinary proof building via scripts/verify.py also works on Linux.')
    commands = [['bootstrap.py'], ['prepare_verification_tools.py']]
    if not args.resume:
        commands.append(['prepare_independent.py', '--work-dir', str(args.work_dir.resolve())])
    commands += [[s] for s in ['build_independent.py', 'replay_independent.py',
                               'check_independent.py', 'report_independent.py']]
    for script, *arguments in commands:
        print('Running ' + script, flush=True)
        subprocess.run([sys.executable, str(ROOT / 'scripts' / script), *arguments],
                       cwd=ROOT, check=True)


if __name__ == '__main__':
    main()

