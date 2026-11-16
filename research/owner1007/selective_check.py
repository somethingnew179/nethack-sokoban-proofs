#!/usr/bin/env python3
"""Small source-checked Lean builds; never a whole-package PASS receipt."""
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location("package_verifier", REPO / "scripts/verify.py")
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def resolve(module):
    root = HERE if module.startswith("Owner1007.") else REPO / "lean"
    return root / (module.replace(".", "/") + ".lean")

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("modules", nargs="+")
    p.add_argument("--cache", default="/private/tmp/nethack-owner1007-lean4331")
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--memory-mb", type=int, default=4096)
    a = p.parse_args()
    cache = Path(a.cache).resolve()
    cache.mkdir(parents=True, exist_ok=True)
    # Hold this lock for the entire build/replay transaction: records.json
    # is a single shared receipt store and must have exactly one writer.
    writer_lock = (cache / ".writer.lock").open("a+")
    try:
        fcntl.flock(writer_lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print(json.dumps({"error": "selective cache already has a writer", "cache": str(cache), "exit": 73}), flush=True)
        return 73
    out = cache / "oleans"
    out.mkdir(exist_ok=True)
    logs = cache / "logs"
    logs.mkdir(exist_ok=True)
    tc = v.resolve_toolchain()
    pin = {k: tc[k] for k in ("lean_version_line", "lean_binary_sha256", "toolchain_file")}
    metadata = cache / "toolchain.json"
    if metadata.exists():
        assert json.loads(metadata.read_text()) == pin, "toolchain cache mismatch"
    metadata.write_text(json.dumps(pin, indent=2) + "\n")
    graph = v.ImportGraph(resolve)
    records_file = cache / "records.json"
    records = json.loads(records_file.read_text()) if records_file.exists() else {}
    env = {"LEAN_PATH": str(out), "PATH": str(Path(tc["lean"]).parent) + ":/usr/bin:/bin"}
    checked = {}
    for module in graph.topological(a.modules):
        source = resolve(module)
        olean = out / (module.replace(".", "/") + ".olean")
        dependencies = {m: checked[m] for m in graph.imports(module)}
        identity = {"source_sha256": digest(source), "dependencies": dependencies, "toolchain": pin}
        old = records.get(module, {})
        if old.get("identity") == identity and olean.exists() and digest(olean) == old.get("olean_sha256"):
            checked[module] = old["olean_sha256"]
            continue
        olean.parent.mkdir(parents=True, exist_ok=True)
        olean.unlink(missing_ok=True)
        root = HERE if module.startswith("Owner1007.") else REPO / "lean"
        command = [tc["lean"], "-R", ".", "-j1", f"-M{a.memory_mb}", "-o", str(olean), str(source.relative_to(root))]
        started = time.monotonic()
        log = logs / (module + ".log")
        with log.open("w") as f:
            try:
                result = subprocess.run(command, cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=a.timeout)
            except subprocess.TimeoutExpired:
                f.write(f"\nTIMEOUT after {a.timeout} seconds\n")
                result = subprocess.CompletedProcess(command,124)
        record = {"identity": identity, "command": command, "cwd": str(root), "exit": result.returncode,
                  "wall_s": round(time.monotonic()-started, 3), "log_sha256": digest(log)}
        if result.returncode == 0 and olean.exists() and "declaration uses 'sorry'" not in log.read_text():
            record["olean_sha256"] = digest(olean)
            checked[module] = record["olean_sha256"]
        records[module] = record
        if result.returncode:
            olean.unlink(missing_ok=True)
        records_file.write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps({"module": module, "exit": result.returncode, "wall_s": record["wall_s"]}), flush=True)
        if module not in checked:
            print(log.read_text())
            return 1
    for module in a.modules:
        command = [tc["leanchecker"], module]
        result = subprocess.run(command, cwd=REPO / "lean", env=env, capture_output=True, text=True, timeout=a.timeout)
        log = logs / (module + ".replay.log")
        log.write_text(result.stdout + result.stderr)
        records[module]["replay"] = {"command": command, "exit": result.returncode, "log_sha256": digest(log)}
        records_file.write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps({"replay": module, "exit": result.returncode}), flush=True)
        if result.returncode:
            print(log.read_text())
            return result.returncode
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
