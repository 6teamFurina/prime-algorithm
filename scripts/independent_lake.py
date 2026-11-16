#!/usr/bin/env python3
"""Run the pinned Lake in the isolated source-only verification workspace."""
from pathlib import Path
import json
import os
import sys

root=Path(__file__).resolve().parents[1]
work=Path(json.loads((root/'verification/local/independent-preparation.json').read_text())['workspace'])
toolchain=root/'.elan/toolchains/leanprover--lean4---v4.33.1'
env=os.environ.copy()
for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','ELAN_TOOLCHAIN','LAKE_HOME','LD_LIBRARY_PATH','DYLD_LIBRARY_PATH','LAKE_OVERRIDE_LEAN','LAKE_CONFIG','LAKE_PKG_URL_MAP']:
    env.pop(key,None)
env.update({
    'PATH':str(toolchain/'bin')+':/usr/bin:/bin:/usr/sbin:/sbin',
    'MATHLIB_NO_CACHE_ON_UPDATE':'1',
    'MATHLIB_CACHE_DIR':str(work/'.disabled-mathlib-cache'),
    'LAKE_NO_CACHE':'1',
    'LAKE_CACHE_DIR':'',
    'LAKE_ARTIFACT_CACHE':'false',
    'LAKE_RESTORE_ARTIFACTS':'false',
    'LEAN_NUM_THREADS':'6',
})
os.chdir(work)
os.execve(str(toolchain/'bin/lake'),['lake','--no-cache',*sys.argv[1:]],env)
