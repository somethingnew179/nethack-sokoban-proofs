#!/usr/bin/env python3
"""Kernel-check one research source against a validated immutable cache snapshot.

This writes a source/command/log record, never compiler outputs or cache metadata.
It is useful while the sole cache writer checks a separate dependency closure.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from selective_check import HERE, REPO, resolve, v


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module')
    parser.add_argument('--memory-mb', type=int, default=8192)
    args = parser.parse_args()
    assert args.module.startswith('Owner1007.')
    source = resolve(args.module)
    cache = Path('/private/tmp/nethack-owner1007-lean4331')
    records = json.loads((HERE/'nethack-owner1007-lean4331-records.json').read_text())
    toolchain = v.resolve_toolchain()
    pin = {k: toolchain[k] for k in ('lean_version_line','lean_binary_sha256','toolchain_file')}
    graph = v.ImportGraph(resolve)
    checked = {}
    for module in graph.topological([args.module]):
        if module == args.module:
            continue
        record = records[module]
        identity = dict(source_sha256=sha(resolve(module)),
                        dependencies={m:checked[m] for m in graph.imports(module)}, toolchain=pin)
        assert identity == record['identity'], module
        output = cache/'oleans'/(module.replace('.','/')+'.olean')
        assert record['exit'] == 0 and sha(output) == record['olean_sha256'], module
        checked[module] = record['olean_sha256']
    code = source.read_text()
    assert v.FORBIDDEN.search(v.COMMENT_OR_STRING.sub(lambda m:m.group(0) if m.group(0)[0]=='"' else ' ',code)) is None
    assert set(v.SET_OPTION.findall(source.read_bytes())) <= v.ALLOWED_OPTIONS
    command = [toolchain['lean'],'--stdin','-j1',f'-M{args.memory_mb}']
    start = time.monotonic()
    try:
        result = subprocess.run(command,input=code,cwd=REPO/'lean',capture_output=True,text=True,
            env={'LEAN_PATH':str(cache/'oleans'),'PATH':str(Path(toolchain['lean']).parent)+':/usr/bin:/bin'},timeout=600)
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ''
        if isinstance(output,bytes):
            output = output.decode(errors='replace')
        result = subprocess.CompletedProcess(command,124,output,'\nTIMEOUT after600 seconds\n')
    log = HERE/(args.module+'.stdin.log')
    log.write_text(result.stdout+result.stderr)
    axioms = {name:[a.strip() for a in listed.split(',') if a.strip()]
              for name,listed in re.findall(r"'([^']+)'\s+depends\s+on\s+axioms:\s+\[([^\]]*)\]",log.read_text())}
    assert all(set(a) <= v.ALLOWED_AXIOMS for a in axioms.values())
    record = dict(module=args.module,source_sha256=sha(source),command=command,cwd=str(REPO/'lean'),
                  exit=result.returncode,wall_s=round(time.monotonic()-start,3),axioms=axioms,
                  log=str(log.relative_to(REPO)),log_sha256=sha(log),dependencies=checked,
                  scope='fresh kernel stdin check; olean/leanchecker replay pending sole cache writer')
    (HERE/(args.module+'.stdin.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:record[k] for k in ('module','exit','wall_s','source_sha256','scope')}),flush=True)
    if result.returncode:
        print(log.read_text())
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
