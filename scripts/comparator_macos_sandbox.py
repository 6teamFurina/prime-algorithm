#!/usr/bin/env python3
"""Run Comparator's Landrun requests using macOS Seatbelt.

Source files remain read-only. Only the explicitly requested writable paths and
/dev are writable; network access is denied. This is a native macOS adapter,
not the upstream Linux Landrun implementation.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

def quoted(value):
    return json.dumps(str(value))

def main():
    args=sys.argv[1:]
    writes=[]
    execs=[]
    env_names=[]
    i=0
    while i<len(args) and args[i]!='--':
        flag=args[i]
        if flag in ('--ro','--rox','--rw','--rwx','--env'):
            value=args[i+1]
            if flag in ('--rw','--rwx'): writes.append(str(Path(value).resolve()))
            if flag in ('--rox','--rwx'): execs.append(str(Path(value).resolve()))
            if flag=='--env': env_names.append(value)
            i+=2
        elif flag in ('--best-effort','-ldd','-add-exec'):
            i+=1
        else:
            raise SystemExit('unsupported Landrun flag: '+flag)
    if i>=len(args): raise SystemExit('missing command separator')
    command=args[i+1:]
    if not command: raise SystemExit('missing command')
    resolved=shutil.which(command[0])
    if not resolved: raise SystemExit('command not found: '+command[0])
    command[0]=str(Path(resolved).resolve())
    if Path(command[0]).name == "lake":
        command.insert(1,"--no-cache")
    profile=['(version 1)','(deny default)',
             '(allow file-read*)','(allow process-fork)','(allow sysctl-read)',
             '(allow signal (target self))',
             '(allow process-exec (literal '+quoted(command[0])+'))']
    for path in writes:
        profile.append('(allow file-write* (subpath '+quoted(path)+'))')
    for path in execs:
        profile.append('(allow process-exec (subpath '+quoted(path)+'))')
    env={k:os.environ[k] for k in env_names if k in os.environ}
    env.update({"MATHLIB_NO_CACHE_ON_UPDATE":"1", "LAKE_NO_CACHE":"1",
                "LAKE_ARTIFACT_CACHE":"false", "LAKE_RESTORE_ARTIFACTS":"false",
                "LAKE_CACHE_DIR":"", "MATHLIB_CACHE_DIR":str(Path.cwd()/".disabled-mathlib-cache"),
                "LEAN_NUM_THREADS":"6"})
    proc=subprocess.run(['/usr/bin/sandbox-exec','-p','\n'.join(profile),*command],env=env)
    raise SystemExit(proc.returncode)

if __name__=='__main__': main()
