#!/usr/bin/env python3
"""Install the independent-checking tools inside this workspace.

Prerequisites: git, a C compiler (Xcode Command Line Tools on macOS), and elan
(either .elan/bin/elan here or available on PATH). ELAN_HOME is always this
project's .elan directory. No global installation or source-digest sweep occurs.

Existing executables are reused. --reuse-only forbids downloads and builds,
while still recording repository revisions and actual executable version probes.
"""
from pathlib import Path
import argparse
import datetime
import json
import os
import platform
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
TOOLS=ROOT/'external/verification-tools'
RESEARCH=ROOT/'verification/local'
COMPARATOR_REV='575674928e239f5bc452aab72d1dd7b0f1326494'
EXPORTER_REV='15f6055e299ad5b89345e533cc2192f4cc00f659'
EXPORTER_TAG='v4.33.0'
PROJECT_LEAN='v4.33.1'
COMPARATOR_LEAN='v4.34.0-rc1'
NANODA_LEAN='v4.35.0'
NANODA_VERSION='0.4.19'


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-only',action='store_true',help='Refuse downloads or compilation; inspect existing tools only')
    args=parser.parse_args()
    if platform.system()!='Darwin':
        raise SystemExit('This runner configures the native macOS sandbox. Use upstream Landrun on Linux.')
    TOOLS.mkdir(parents=True,exist_ok=True)
    RESEARCH.mkdir(exist_ok=True)
    logfile=RESEARCH/'independent-tools-prepare.log'
    reportfile=RESEARCH/'independent-tools.json'
    data={'status':'running','started_utc':now(),'installation_root':str(TOOLS),
          'elan_home':str(ROOT/'.elan'),'reuse_only':args.reuse_only,'commands':[],
          'source_digest_audits':False}
    env=os.environ.copy()
    env['ELAN_HOME']=str(ROOT/'.elan')
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','ELAN_TOOLCHAIN','LAKE_HOME'):
        env.pop(key,None)

    def save():
        reportfile.write_text(json.dumps(data,indent=2)+'\n')

    def run(cmd,cwd=ROOT,runenv=None,summary_only=False):
        cmd=[str(x) for x in cmd]
        result=subprocess.run(cmd,cwd=cwd,env=runenv or env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        output=result.stdout
        data['commands'].append({'argv':cmd,'cwd':str(cwd),'exit_code':result.returncode,
                                 'output':output.splitlines()[0] if summary_only and output else output})
        with logfile.open('a') as log:
            log.write(json.dumps({'argv':cmd,'cwd':str(cwd)},ensure_ascii=False)+'\n')
            log.write(output+'\n')
        save()
        if result.returncode: raise RuntimeError('Command failed; see '+str(logfile))
        return output.strip()

    def checkout(name,url,revision):
        source=TOOLS/name
        if not source.exists():
            if args.reuse_only: raise RuntimeError('Missing repository: '+str(source))
            run(['git','clone','--filter=blob:none',url,source])
            run(['git','-C',source,'checkout','--detach',revision])
        actual=run(['git','-C',source,'rev-parse','HEAD'])
        if actual!=revision:
            raise RuntimeError('Existing '+name+' is at another revision; refusing to reset it')
        return source

    def toolchain(version):
        prefix=ROOT/'.elan/toolchains'/('leanprover--lean4---'+version)
        if not (prefix/'bin/lean').is_file():
            if args.reuse_only: raise RuntimeError('Missing Lean toolchain: '+version)
            local=ROOT/'.elan/bin/elan'
            elan=str(local) if local.is_file() else shutil.which('elan')
            if not elan: raise RuntimeError('Install elan first, or provide .elan/bin/elan in this workspace')
            run([elan,'toolchain','install','leanprover/lean4:'+version])
        actual=run([prefix/'bin/lean','--version'])
        if version.removeprefix('v') not in actual:
            raise RuntimeError('Unexpected Lean version: '+actual)
        return prefix,actual

    def build(source,prefix,target):
        binary=source/'.lake/build/bin'/target
        reused=binary.is_file() and os.access(binary,os.X_OK)
        if not reused:
            if args.reuse_only: raise RuntimeError('Missing executable: '+str(binary))
            buildenv=env.copy();buildenv['PATH']=str(prefix/'bin')+':'+env.get('PATH','')
            run([prefix/'bin/lake','--no-cache','build',target],cwd=source,runenv=buildenv)
        return binary,reused

    try:
        comparator_source=checkout('comparator','https://github.com/leanprover/comparator.git',COMPARATOR_REV)
        exporter_source=checkout('lean4export','https://github.com/leanprover/lean4export.git',EXPORTER_REV)
        cmp_prefix,cmp_version=toolchain(COMPARATOR_LEAN)
        project_prefix,project_version=toolchain(PROJECT_LEAN)
        nano_prefix,nano_lean_version=toolchain(NANODA_LEAN)
        comparator,reused_cmp=build(comparator_source,cmp_prefix,'comparator')
        exporter,reused_exp=build(exporter_source,project_prefix,'lean4export')
        nano=nano_prefix/'bin/nanoda_bin'
        if not nano.is_file(): raise RuntimeError('Pinned official Lean '+NANODA_LEAN+' is missing nanoda_bin')
        nano_help=run([nano,'--help'],summary_only=True)
        if nano_help.splitlines()[0]!='nanoda_bin '+NANODA_VERSION:
            raise RuntimeError('Unexpected nanoda version: '+nano_help.splitlines()[0])
        probeenv=env.copy();probeenv['PATH']=str(project_prefix/'bin')+':'+env.get('PATH','')
        metadata=json.loads(run([exporter,'--'],runenv=probeenv))['meta']
        if metadata['lean']['version']!='4.33.1': raise RuntimeError('Exporter was compiled with another Lean version')
        data.update({
          'status':'ready','finished_utc':now(),
          'comparator':{'repository':'https://github.com/leanprover/comparator','revision':COMPARATOR_REV,
                        'binary':str(comparator),'build_toolchain':cmp_version,'reused_binary':reused_cmp,
                        'note':'The pinned upstream Comparator has its own Lean 4.34.0-rc1 build toolchain; it replays the serialized 4.33.1 proof export.'},
          'exporter':{'repository':'https://github.com/leanprover/lean4export','tag':EXPORTER_TAG,
                      'revision':EXPORTER_REV,'binary':str(exporter),'build_toolchain':project_version,
                      'reused_binary':reused_exp,'metadata':metadata,
                      'note':'Upstream CI patch fallback: v4.33.0 exporter source compiled with project Lean 4.33.1.'},
          'nanoda':{'binary':str(nano),'version':NANODA_VERSION,'source':'Official Lean '+NANODA_LEAN+' binary distribution',
                    'distribution_url':'https://github.com/leanprover/lean4/releases/tag/'+NANODA_LEAN,
                    'distribution_lean_version':nano_lean_version,
                    'note':'Independent Rust kernel, version 0.4.19; intentionally records the difference from upstream CI old 0.4.6-beta pin.'},
          'sandbox':{'kind':'macOS Seatbelt','adapter':str(ROOT/'scripts/comparator_macos_sandbox.py'),
                     'policy':'Default deny; source files read-only, explicit build directories writable, no network or Mach services.'},
          'next_command':'python3 scripts/check_independent.py',
          'upstream_ci':'https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/.github/scripts/comparator-check.sh'
        })
        save()
        print('Verification tools ready; version probes recorded in '+str(reportfile))
    except Exception as error:
        data.update({'status':'failed','error':str(error),'finished_utc':now()});save()
        raise

if __name__=='__main__': main()
