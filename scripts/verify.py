#!/usr/bin/env python3
"""Sequential, source-only verification of the packaged Sokoban push-count proofs.

  python3 scripts/verify.py check
  python3 scripts/verify.py build --build-dir ../build-clean [--root 4-2 ...]
  python3 scripts/verify.py receipt --build-dir ../build-clean
  python3 scripts/verify.py check-receipt

`build` compiles every module of the import closure once, one single-threaded
`lean` process at a time. LEAN_PATH contains only the build directory, which
must start empty, so nothing but this repository's sources can be imported.
Oleans no later root needs are deleted after each root's audit passes, which
keeps the peak disk use near the largest single closure. An interrupted build
resumes from its records; a resume re-hashes the oleans it keeps.

`check-receipt` only cross-checks recorded results against the manifest. It is
not a fresh verification: only `build` is. Python standard library only.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO / "lean"
SPEC = json.loads((REPO / "roots.json").read_text())
ROOTS = {r["id"]: r for r in SPEC["roots"]}
ALLOWED_AXIOMS = set(SPEC["allowed_axioms"])
MANIFEST = REPO / "MANIFEST.sha256"
RECEIPT = REPO / "VERIFICATION_RECEIPT.json"
RECEIPTS_DIR = REPO / "receipts"
# Written after the build, so they cannot be covered by the manifest they cite.
RESULT_PATHS = ("README.md", "README_RU.md", "RESULT_RU.md", "VERIFICATION_RECEIPT.json", "receipts/")

EXIT_FAILED, EXIT_DISK, EXIT_TERMINATED = 1, 75, 143

# Outside comments none of these may appear; `#print axioms` is the actual gate.
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|native_decide|axiom|unsafe|implemented_by|extern|opaque|partial"
    r"|initialize|builtin_initialize|include_str|run_cmd|run_elab|run_meta|elab|macro"
    r"|syntax|csimp|ofReduceBool|ofReduceNat|reduceBool|reduceNat|trustCompiler"
    r"|skipKernelTC|readFile)\b|IO\.FS|#eval|\+native"
)
FORBIDDEN_BYTES = [t.encode() for t in (
    "sorry admit native_decide axiom unsafe implemented_by extern opaque partial initialize "
    "include_str run_cmd run_elab run_meta elab macro syntax csimp educeBool educeNat trustCompiler "
    "skipKernelTC readFile IO.FS #eval +native").split()]
COMMENT_OR_STRING = re.compile(r'"(?:[^"\\]|\\.)*"|/-.*?-/|--[^\n]*', re.S)
ALLOWED_OPTIONS = {b"maxRecDepth", b"maxHeartbeats", b"linter.unusedSimpArgs", b"linter.unusedVariables"}
SET_OPTION = re.compile(rb"set_option\s+([A-Za-z.]+)")
PRIVATE_PATTERNS = [p.encode() for p in (
    "/Users/ /home/ /private/ /root/ api_key API_KEY password Bearer ghp_ tg: telegram Telegram "
    "@gmail @yandex").split()]

MODULE_KEYWORD = re.compile(r"(?:module|prelude)\b")
IMPORT = re.compile(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)")


def git(*arguments: str) -> subprocess.CompletedProcess:
    """Run git on this repository only; the ceiling stops it climbing into an enclosing one."""
    return subprocess.run(["git", "-C", str(REPO), *arguments], capture_output=True, text=True,
                          env={**os.environ, "GIT_CEILING_DIRECTORIES": str(REPO.parent)})


def utc_now() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    os.replace(temporary, path)


def source_path(module: str) -> Path:
    return LEAN_DIR / (module.replace(".", "/") + ".lean")


def parse_imports(text: str) -> list[str]:
    """Imports from a Lean file header, skipping nested block and line comments."""
    position, end, found = 0, len(text), []
    while True:
        while position < end:
            if text[position].isspace():
                position += 1
            elif text.startswith("--", position):
                newline = text.find("\n", position)
                position = end if newline < 0 else newline + 1
            elif text.startswith("/-", position):
                depth, position = 1, position + 2
                while position < end and depth:
                    if text.startswith("/-", position):
                        depth, position = depth + 1, position + 2
                    elif text.startswith("-/", position):
                        depth, position = depth - 1, position + 2
                    else:
                        position += 1
            else:
                break
        keyword = MODULE_KEYWORD.match(text, position)
        if keyword:
            position = keyword.end()
            continue
        match = IMPORT.match(text, position)
        if not match:
            return found
        found.append(match.group(1))
        position = match.end()


class ImportGraph:
    """Import edges of local modules; `Init*` modules come from the toolchain."""

    def __init__(self, resolve=source_path):
        self.resolve = resolve
        self.edges: dict[str, list[str]] = {}
        self.external: set[str] = set()

    def imports(self, module: str) -> list[str]:
        if module not in self.edges:
            path = self.resolve(module)
            if not path.exists():
                raise FileNotFoundError(f"{module}: no source at {path}")
            with path.open(encoding="utf-8") as handle:
                local = []
                for name in parse_imports(handle.read(1 << 18)):
                    if name == "Init" or name.startswith("Init."):
                        self.external.add(name)
                    else:
                        local.append(name)
            self.edges[module] = local
        return self.edges[module]

    def closure(self, start: list[str]) -> set[str]:
        seen: set[str] = set()
        stack = list(start)
        while stack:
            module = stack.pop()
            if module not in seen:
                seen.add(module)
                stack.extend(self.imports(module))
        return seen

    def topological(self, start: list[str]) -> list[str]:
        """Dependencies first; deterministic for a given set of sources."""
        order: list[str] = []
        state: dict[str, int] = {}
        for first in sorted(start):
            if first in state:
                continue
            stack = [(first, iter(sorted(self.imports(first))))]
            state[first] = 1
            while stack:
                module, pending = stack[-1]
                for child in pending:
                    if child not in state:
                        state[child] = 1
                        stack.append((child, iter(sorted(self.imports(child)))))
                        break
                    if state[child] == 1:
                        raise ValueError(f"import cycle through {child}")
                else:
                    stack.pop()
                    state[module] = 2
                    order.append(module)
        return order


def root_closure(graph: ImportGraph, root_id: str) -> set[str]:
    """Modules to compile for a root: everything its audit module imports."""
    return graph.closure(graph.imports(ROOTS[root_id]["audit_module"]))


def read_manifest() -> dict[str, str]:
    entries = {}
    for line in MANIFEST.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        entries[relative] = digest
    return entries


def resolve_toolchain() -> dict:
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=LEAN_DIR, text=True).strip()
    lean = Path(prefix) / "bin" / "lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    pin = SPEC["toolchain"]
    match = re.fullmatch(r"Lean \(version ([0-9.]+), ([^,]+), commit ([0-9a-f]+), Release\)", version)
    if not match or match.group(1) != pin["version"] or match.group(3) != pin["commit"]:
        raise SystemExit(f"FAIL toolchain: got {version!r}, need {pin['version']} commit {pin['commit']}")
    lake = Path(prefix) / "bin" / "lake"
    return dict(
        lean=str(lean), lean_version_line=version, lean_binary_sha256=sha256_file(lean), platform=match.group(2),
        lake_version_line=subprocess.check_output([str(lake), "--version"], text=True).strip(),
        toolchain_file=(LEAN_DIR / "lean-toolchain").read_text().strip(),
        leanchecker=str(Path(prefix) / "bin" / "leanchecker"),
    )


def check_manifest() -> dict:
    entries = read_manifest()
    mismatched = [p for p, d in entries.items() if not (REPO / p).is_file() or sha256_file(REPO / p) != d]
    tracked = git("ls-files")
    unlisted = []
    if tracked.returncode == 0 and tracked.stdout:
        unlisted = [p for p in tracked.stdout.splitlines()
                    if p != "MANIFEST.sha256" and p not in entries and not p.startswith(RESULT_PATHS)]
    if mismatched or unlisted:
        raise SystemExit(f"FAIL manifest: mismatched {mismatched[:10]} unlisted {unlisted[:10]}")
    return dict(files=len(entries), manifest_sha256=sha256_file(MANIFEST))


def check_closure() -> dict:
    graph = ImportGraph()
    union: set[str] = set()
    for root_id in ROOTS:
        union |= root_closure(graph, root_id)
    on_disk = {".".join(p.relative_to(LEAN_DIR).with_suffix("").parts) for p in (LEAN_DIR / "NetHack").rglob("*.lean")}
    if union != on_disk:
        raise SystemExit(f"FAIL closure: missing {sorted(union - on_disk)[:10]} extra {sorted(on_disk - union)[:10]}")
    stray = [str(p) for p in LEAN_DIR.rglob("*") if p.suffix in (".olean", ".ilean", ".c", ".o", ".trace", ".hash")]
    if stray:
        raise SystemExit(f"FAIL prebuilt artifacts in tree: {stray[:10]}")
    return dict(modules=len(union), source_bytes=sum(source_path(m).stat().st_size for m in union),
                external_imports=sorted(graph.external))


def check_sources() -> dict:
    forbidden, options, private = [], set(), []
    modules = [".".join(p.relative_to(LEAN_DIR).with_suffix("").parts) for p in LEAN_DIR.rglob("*.lean")]
    for module in modules:
        raw = source_path(module).read_bytes()
        if any(token in raw for token in FORBIDDEN_BYTES):
            text = raw.decode("utf-8")
            code = COMMENT_OR_STRING.sub(lambda m: m.group(0) if m.group(0)[0] == '"' else " ", text)
            hit = FORBIDDEN.search(code)
            if hit:
                forbidden.append((module, hit.group(0)))
        if b"set_option" in raw:
            options.update(SET_OPTION.findall(raw))
        if any(token in raw for token in PRIVATE_PATTERNS):
            private.append(module)
    if forbidden or options - ALLOWED_OPTIONS or private:
        raise SystemExit(f"FAIL source scan: {forbidden[:10]} options {options - ALLOWED_OPTIONS} private {private[:10]}")
    return dict(modules_scanned=len(modules), options_used=sorted(o.decode() for o in options))


def check_map_generation() -> dict:
    """The map data must be regenerated byte-for-byte from the pinned Lua files."""
    environment = {"PATH": "/usr/bin:/bin", "PYTHONDONTWRITEBYTECODE": "1"}
    source = LEAN_DIR / "validation/sokoban/source"
    outputs = {}
    for script in ("extract.py", "generate_lean.py"):
        done = subprocess.run([sys.executable, str(source / script), "--check"], env=environment,
                              capture_output=True, text=True)
        if done.returncode:
            raise SystemExit(f"FAIL {script}: {done.stdout}{done.stderr}")
        outputs[script] = done.stdout.splitlines()[0]
    return outputs


def cmd_check(_args=None) -> dict:
    result = {}
    for name, step in (("toolchain", resolve_toolchain), ("manifest", check_manifest), ("closure", check_closure),
                       ("source_scan", check_sources), ("map_generation", check_map_generation)):
        started = time.monotonic()
        result[name] = step()
        print(f"PASS {name} ({time.monotonic() - started:.1f}s): {json.dumps(result[name], ensure_ascii=False)}", flush=True)
    return result


class Terminated(Exception):
    pass


class Build:
    def __init__(self, args):
        self.args = args
        self.dir = Path(args.build_dir).resolve()
        if self.dir == REPO or REPO in self.dir.parents:
            raise SystemExit("FAIL: the build directory must be outside the repository")
        self.oleans = self.dir / "oleans"
        self.records = self.dir / "records"
        self.logs = self.dir / "logs"
        self.graph = ImportGraph()
        self.child = None
        self.ok: dict[str, dict] = {}
        self.disk_bytes = self.peak_disk_bytes = 0
        self.min_free = shutil.disk_usage(self.dir.parent).free
        self.compiled_now = 0
        self.started = time.monotonic()

    def environment(self) -> dict:
        # The pinned bin comes first: leanchecker asks `lean` on PATH for its sysroot.
        return {"LEAN_PATH": str(self.oleans), "PATH": f"{Path(self.toolchain['lean']).parent}:/usr/bin:/bin",
                "HOME": str(self.dir / "home"), "TMPDIR": os.environ.get("TMPDIR", "/tmp")}

    def olean(self, module: str) -> Path:
        return self.oleans / (module.replace(".", "/") + ".olean")

    def event(self, kind: str, **fields) -> None:
        with (self.records / "events.jsonl").open("a") as handle:
            handle.write(json.dumps(dict(event=kind, utc=utc_now(), **fields)) + "\n")

    def status(self, state: str, **fields) -> None:
        write_json(self.dir / "status.json", dict(
            state=state, utc=utc_now(), modules_ok=len(self.ok), compiled_this_process=self.compiled_now,
            process_elapsed_s=round(time.monotonic() - self.started, 1), olean_bytes_on_disk=self.disk_bytes,
            peak_olean_bytes=self.peak_disk_bytes, min_free_bytes=self.min_free, **fields))

    def run_measured(self, command: list[str], log: Path) -> dict:
        """Run one child; os.wait4 gives its own rusage without a helper binary."""
        started = time.monotonic()
        with log.open("wb") as output:
            self.child = subprocess.Popen(command, env=self.environment(), cwd=LEAN_DIR, stdout=output,
                                          stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        delay, timed_out = 0.002, False
        while True:
            pid, status, usage = os.wait4(self.child.pid, os.WNOHANG)
            if pid:
                break
            if time.monotonic() - started > self.args.timeout_s:
                self.child.kill()
                pid, status, usage = os.wait4(self.child.pid, 0)
                timed_out = True
                break
            time.sleep(delay)
            delay = min(delay * 1.5, 0.1)
        self.child.returncode = os.waitstatus_to_exitcode(status)
        code = self.child.returncode
        self.child = None
        scale = 1 if platform.system() == "Darwin" else 1024
        return dict(exit=code, timed_out=timed_out, wall_s=round(time.monotonic() - started, 3),
                    user_s=round(usage.ru_utime, 3), sys_s=round(usage.ru_stime, 3), max_rss_bytes=usage.ru_maxrss * scale)

    def lean_command(self, *rest: str) -> list[str]:
        return [self.toolchain["lean"], "-R", ".", "-j1", f"-M{self.args.memory_mib}", *rest]

    def guard_disk(self) -> None:
        free = shutil.disk_usage(self.dir).free
        self.min_free = min(self.min_free, free)
        if free < self.args.min_free_mib * 2**20:
            self.event("blocked_disk", free_bytes=free)
            self.status("BLOCKED_DISK", free_bytes=free)
            print(f"BLOCKED: {free} bytes free, below --min-free-mib; free space and rerun to resume", flush=True)
            raise SystemExit(EXIT_DISK)

    def compile(self, module: str, root_id: str) -> None:
        self.guard_disk()
        source = source_path(module)
        relative = str(source.relative_to(REPO))
        digest = sha256_file(source)
        if digest != self.manifest.get(relative):
            raise SystemExit(f"FAIL {module}: source hash differs from the manifest")
        output = self.olean(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.unlink(missing_ok=True)
        log = self.logs / (module + ".log")
        measured = self.run_measured(self.lean_command("-o", str(output), str(source.relative_to(LEAN_DIR))), log)
        record = dict(module=module, root_stage=root_id, source_sha256=digest, memory_limit_mib=self.args.memory_mib,
                      utc=utc_now(), log_bytes=log.stat().st_size, **measured)
        passed = measured["exit"] == 0 and output.is_file()
        if passed and b"declaration uses 'sorry'" in log.read_bytes():
            passed = False
            record["failure"] = "log reports sorry"
        if passed:
            record["olean_bytes"] = output.stat().st_size
            record["olean_sha256"] = sha256_file(output)
        with (self.records / "modules.jsonl").open("a") as handle:
            handle.write(json.dumps(record) + "\n")
        if not passed:
            self.status("FAILED", module=module, exit=measured["exit"], log=str(log))
            print(f"FAILED {module}: exit {measured['exit']}; log {log}\n{log.read_text(errors='replace')[-3000:]}", flush=True)
            raise SystemExit(EXIT_FAILED)
        if record["log_bytes"] == 0:
            log.unlink()
        self.ok[module] = record
        self.disk_bytes += record["olean_bytes"]
        self.peak_disk_bytes = max(self.peak_disk_bytes, self.disk_bytes)
        self.compiled_now += 1
        self.status("RUNNING", root=root_id, last_module=module)

    def audit(self, root_id: str) -> dict:
        root = ROOTS[root_id]
        log = self.records / f"audit-{root_id}.txt"
        audit_source = str(source_path(root["audit_module"]).relative_to(LEAN_DIR))
        measured = self.run_measured(self.lean_command(audit_source), log)
        text = log.read_text(errors="replace")
        axioms: dict[str, list[str]] = {}
        # Lean wraps long messages, so any whitespace run may be a line break.
        for name, listed in re.findall(r"'([^']+)'\s+depends\s+on\s+axioms:\s+\[([^\]]*)\]", text):
            axioms[name] = [a.strip() for a in listed.split(",") if a.strip()]
        for name in re.findall(r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", text):
            axioms[name] = []
        missing = [k for k in root["axiom_audit_keys"] if k not in axioms]
        disallowed = {k: sorted(set(v) - ALLOWED_AXIOMS) for k, v in axioms.items() if set(v) - ALLOWED_AXIOMS}
        errors = len(re.findall(r"^\S+: error|: error:", text, re.M))
        replay = self.run_measured([self.toolchain["leanchecker"], root["module"]], self.records / f"replay-{root_id}.txt")
        passed = measured["exit"] == 0 and not missing and not disallowed and not errors and replay["exit"] == 0
        result = dict(root=root_id, audit_module=root["audit_module"], audit_source_sha256=sha256_file(source_path(root["audit_module"])),
                      audit_output_sha256=sha256_file(log), status="PASS" if passed else "FAIL", utc=utc_now(), **measured,
                      axioms=axioms, missing_keys=missing, disallowed=disallowed,
                      supplementary_kernel_replay_of_root_module=replay)
        write_json(self.records / f"audit-{root_id}.json", result)
        if not passed:
            self.status("FAILED", root=root_id, audit=result["status"])
            print(f"FAILED audit {root_id}:\n{text[-3000:]}\nmissing={missing} disallowed={disallowed} replay={replay}", flush=True)
            raise SystemExit(EXIT_FAILED)
        return result

    def resume_or_start(self) -> None:
        if not self.records.exists():
            if any(entry.name != "LOCK" for entry in self.dir.iterdir()):
                raise SystemExit(f"FAIL: {self.dir} is not empty and holds no build records; a clean build needs an empty directory")
            for directory in (self.records, self.logs, self.oleans, self.dir / "home"):
                directory.mkdir(parents=True)
            status = git("status", "--porcelain", "--ignored")
            # An agent harness may place its own .claude/ here; it is ignored by git and outside LEAN_PATH.
            not_clean = "\n".join(line for line in status.stdout.splitlines() if line != "!! .claude/")
            if status.returncode or not_clean:
                if not self.args.allow_dirty:
                    raise SystemExit(f"FAIL: repository is not clean:\n{not_clean[:2000]}{status.stderr}")
            head = git("rev-parse", "HEAD", "HEAD^{tree}")
            commit, tree = head.stdout.split()[:2] if head.returncode == 0 else (None, None)
            write_json(self.records / "run.json", dict(
                started_utc=utc_now(), source_commit=commit, source_tree=tree, git_status_at_start=status.stdout,
                dirty=bool(not_clean), manifest_sha256=sha256_file(MANIFEST), toolchain=self.toolchain,
                check=self.args.check_result, memory_limit_mib=self.args.memory_mib, timeout_s=self.args.timeout_s,
                environment_keys=sorted(self.environment()), lean_path="<build-dir>/oleans only",
                build_command=" ".join(self.args.argv)))
            self.event("start")
            return
        recorded = {}
        modules_file = self.records / "modules.jsonl"
        if modules_file.exists():
            for line in modules_file.read_text().splitlines():
                record = json.loads(line)
                if record["exit"] == 0 and "olean_sha256" in record:
                    recorded[record["module"]] = record
        deleted = set()
        events = self.records / "events.jsonl"
        for line in events.read_text().splitlines():
            event = json.loads(line)
            if event["event"] == "delete_unneeded":
                deleted.update(event["modules"])
        for path in self.oleans.rglob("*.olean"):
            module = ".".join(path.relative_to(self.oleans).with_suffix("").parts)
            record = recorded.get(module)
            if record is None or module in deleted:
                path.unlink()
                continue
            if sha256_file(path) != record["olean_sha256"]:
                raise SystemExit(f"FAIL resume: {path} differs from its record; the build directory is not trustworthy")
            self.disk_bytes += record["olean_bytes"]
        self.peak_disk_bytes = self.disk_bytes
        self.ok = recorded
        self.deleted = deleted
        self.event("resume", recorded=len(recorded), argv=self.args.argv)

    def run(self) -> int:
        self.toolchain = resolve_toolchain()
        self.manifest = read_manifest()
        self.deleted: set[str] = set()
        self.resume_or_start()
        order = [r for r in SPEC["build_order"] if not self.args.root or r in self.args.root]
        closures = {r: root_closure(self.graph, r) for r in ROOTS}
        audited = {r for r in ROOTS if (self.records / f"audit-{r}.json").exists()
                   and json.loads((self.records / f"audit-{r}.json").read_text())["status"] == "PASS"}
        for root_id in order:
            if root_id in audited:
                continue
            self.event("root_start", root=root_id, closure_modules=len(closures[root_id]))
            for module in self.graph.topological(list(closures[root_id])):
                if module in self.deleted:
                    raise SystemExit(f"FAIL: {module} was deleted but root {root_id} needs it")
                if module not in self.ok:
                    self.compile(module, root_id)
            self.guard_disk()
            result = self.audit(root_id)
            audited.add(root_id)
            self.event("root_done", root=root_id, audit_status=result["status"])
            print(f"ROOT {root_id} PASS closure={len(closures[root_id])} modules; axioms {sorted({a for v in result['axioms'].values() for a in v})}", flush=True)
            if not self.args.keep_oleans:
                remaining = [r for r in SPEC["build_order"] if r not in audited]
                still_needed = set().union(*[closures[r] for r in remaining]) if remaining else set()
                removable = sorted(m for m in self.ok if m not in still_needed and m not in self.deleted and self.olean(m).exists())
                freed = 0
                for module in removable:
                    freed += self.ok[module]["olean_bytes"]
                    self.olean(module).unlink()
                self.deleted.update(removable)
                self.disk_bytes -= freed
                self.event("delete_unneeded", after_root=root_id, freed_bytes=freed, modules=removable)
        self.event("done", audited=sorted(audited))
        self.status("DONE", audited=sorted(audited))
        return 0


def cmd_build(args) -> int:
    build = Build(args)
    args.check_result = None
    if not (build.dir / "records").exists():
        args.check_result = cmd_check()

    def terminate(_signum, _frame):
        if build.child:
            build.child.kill()
        raise Terminated

    signal.signal(signal.SIGTERM, terminate)
    signal.signal(signal.SIGINT, terminate)
    build.dir.mkdir(parents=True, exist_ok=True)
    lock = build.dir / "LOCK"
    if lock.exists():
        try:
            os.kill(int(lock.read_text()), 0)
            raise SystemExit(f"FAIL: another build holds {lock}")
        except (ProcessLookupError, ValueError):
            pass
    lock.write_text(str(os.getpid()))
    try:
        return build.run()
    except Terminated:
        build.event("terminated")
        build.status("TERMINATED")
        return EXIT_TERMINATED
    finally:
        lock.unlink(missing_ok=True)


def load_module_records(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines()]


def summarise(values: list[dict]) -> dict:
    peak = max(values, key=lambda r: r["max_rss_bytes"])
    return dict(modules=len(values), wall_s=round(sum(r["wall_s"] for r in values), 1),
                user_s=round(sum(r["user_s"] for r in values), 1), sys_s=round(sum(r["sys_s"] for r in values), 1),
                olean_bytes=sum(r["olean_bytes"] for r in values),
                peak_rss_bytes=peak["max_rss_bytes"], peak_rss_module=peak["module"])


def cmd_receipt(args) -> int:
    build = Path(args.build_dir).resolve()
    records = build / "records"
    run = json.loads((records / "run.json").read_text())
    all_records = load_module_records(records / "modules.jsonl")
    final = {r["module"]: r for r in all_records}
    failed_attempts = [dict(module=r["module"], exit=r["exit"], memory_limit_mib=r["memory_limit_mib"], wall_s=r["wall_s"])
                       for r in all_records if r["exit"] != 0 or "olean_sha256" not in r]
    events = [json.loads(line) for line in (records / "events.jsonl").read_text().splitlines()]
    graph = ImportGraph()
    manifest = read_manifest()
    problems, per_root = [], {}
    for root_id in SPEC["build_order"]:
        root = ROOTS[root_id]
        closure = root_closure(graph, root_id)
        path = records / f"audit-{root_id}.json"
        missing = sorted(m for m in closure if m not in final or "olean_sha256" not in final[m])
        if missing:
            problems.append(f"{root_id}: {len(missing)} modules not compiled")
        audit = json.loads(path.read_text()) if path.exists() else None
        if audit is None or audit["status"] != "PASS":
            problems.append(f"{root_id}: audit did not pass")
        present = [final[m] for m in closure if m in final and "olean_sha256" in final[m]]
        per_root[root_id] = dict(
            level=root["level"], kind=root["kind"], lower=root["lower"], upper=root["upper"], module=root["module"],
            interval_theorem=root["interval_theorem"], lower_bound_theorem=root["lower_bound_theorem"],
            upper_witness_theorems=root["upper_witness_theorems"], upper_witness_moves=root["upper_witness_moves"],
            minimum_theorem=root["minimum_theorem"], supplementary_theorems=root["supplementary_theorems"],
            closure=summarise(present) if present else None,
            closure_source_bytes=sum(source_path(m).stat().st_size for m in closure),
            compiled_in_this_stage=sum(1 for r in present if r["root_stage"] == root_id),
            audit=None if audit is None else {k: audit[k] for k in (
                "status", "audit_module", "audit_source_sha256", "audit_output_sha256", "exit", "wall_s", "user_s", "sys_s",
                "max_rss_bytes", "axioms", "supplementary_kernel_replay_of_root_module")},
            stage_events={e["event"]: e["utc"] for e in events if e.get("root") == root_id},
        )
    for relative, digest in ((str(source_path(m).relative_to(REPO)), r["source_sha256"]) for m, r in final.items()):
        if manifest.get(relative) != digest:
            problems.append(f"{relative}: recorded hash differs from the manifest")
    if run["dirty"] or run["source_commit"] is None:
        problems.append("build did not start from a clean commit")
    if not any(e["event"] == "done" for e in events):
        problems.append("build has not finished")
    manifest_check = check_manifest()
    if manifest_check["manifest_sha256"] != run["manifest_sha256"]:
        problems.append("manifest changed after the build started")
    if failed_attempts:
        problems.append(f"{len(failed_attempts)} failed module attempts are listed in failed_attempts; see them before relying on this receipt")
    disk = json.loads((build / "status.json").read_text())
    resumes = [e["utc"] for e in events if e["event"] == "resume"]
    RECEIPTS_DIR.mkdir(exist_ok=True)
    (RECEIPTS_DIR / "axioms").mkdir(exist_ok=True)
    for root_id in SPEC["build_order"]:
        source = records / f"audit-{root_id}.txt"
        if source.exists():
            shutil.copyfile(source, RECEIPTS_DIR / "axioms" / f"{root_id}.txt")
    with gzip.GzipFile(RECEIPTS_DIR / "modules.jsonl.gz", "wb", mtime=0) as handle:
        for record in all_records:
            handle.write((json.dumps(record, sort_keys=True) + "\n").encode())
    finals = [r for r in final.values() if "olean_sha256" in r]
    receipt = dict(
        schema="nethack-sokoban-verification-receipt-v1",
        status="PASS" if not problems else "WIP",
        problems=problems,
        what_this_is="Results of one clean sequential source build in an isolated directory on the machine described below.",
        source_commit=run["source_commit"], source_tree=run["source_tree"], manifest_sha256=run["manifest_sha256"],
        modules_log_sha256=sha256_file(RECEIPTS_DIR / "modules.jsonl.gz"),
        started_utc=run["started_utc"], finished_utc=next((e["utc"] for e in reversed(events) if e["event"] == "done"), None),
        resumes=resumes, build_command=run["build_command"],
        per_module_command="lean -R . -j1 -M<memory_limit_mib> -o <build-dir>/oleans/<module>.olean <module>.lean  (cwd lean/, LEAN_PATH=<build-dir>/oleans only)",
        toolchain={k: v for k, v in run["toolchain"].items() if k not in ("lean", "leanchecker")},
        lake_packages=SPEC["toolchain"]["lake_packages"],
        environment=dict(os=platform.platform(), machine=platform.machine(), logical_cpus=os.cpu_count(),
                         physical_memory_bytes=os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE"),
                         python=platform.python_version(), concurrency="one lean process at a time, -j1",
                         memory_limit_mib=run["memory_limit_mib"], timeout_s=run["timeout_s"],
                         environment_keys=run["environment_keys"], lean_path=run["lean_path"]),
        pre_build_check={k: ({f: v[f] for f in v if f not in ("lean", "leanchecker")} if k == "toolchain" else v)
                         for k, v in (run["check"] or {}).items()},
        allowed_axioms=sorted(ALLOWED_AXIOMS),
        totals=dict(summarise(finals) if finals else {}, compile_attempts=len(all_records),
                    peak_olean_bytes_on_disk_this_process=disk.get("peak_olean_bytes"), min_free_disk_bytes_this_process=disk.get("min_free_bytes"),
                    modules_with_compiler_messages=sum(1 for r in finals if r["log_bytes"])),
        failed_attempts=failed_attempts,
        roots=per_root,
    )
    write_json(RECEIPT, receipt)
    print(f"{RECEIPT.name}: status {receipt['status']}; problems: {problems or 'none'}")
    return 0 if not problems else EXIT_FAILED


def cmd_check_receipt(_args) -> int:
    """Cross-check only. Compare the recorded results with the current tree; compiles nothing."""
    receipt = json.loads(RECEIPT.read_text())
    problems = list(receipt["problems"])
    manifest = read_manifest()
    records = {}
    with gzip.open(RECEIPTS_DIR / "modules.jsonl.gz", "rt") as handle:
        for line in handle:
            record = json.loads(line)
            records[record["module"]] = record
    graph = ImportGraph()
    expected: set[str] = set()
    for root_id in ROOTS:
        expected |= root_closure(graph, root_id)
    if set(records) != expected:
        problems.append(f"records {len(records)} differ from closure {len(expected)}")
    for module, record in records.items():
        if record["exit"] != 0 or record["source_sha256"] != manifest.get(str(source_path(module).relative_to(REPO))):
            problems.append(f"{module}: bad record")
    if sha256_file(RECEIPTS_DIR / "modules.jsonl.gz") != receipt["modules_log_sha256"]:
        problems.append("modules log differs from the receipt")
    if sha256_file(MANIFEST) != receipt["manifest_sha256"]:
        problems.append("manifest differs from the receipt")
    check_manifest()
    changed = git("diff", "--name-only", receipt["source_commit"], "HEAD", "--", "lean", "dat", "scripts", "docs",
                  "roots.json", "MANIFEST.sha256", "LICENSE", "NOTICE.md", ".gitignore", ".gitattributes")
    if changed.returncode or changed.stdout.strip():
        problems.append(f"verified paths changed since the built commit: {changed.stdout[:500]}{changed.stderr[:200]}")
    for root_id, root in receipt["roots"].items():
        for name, axioms in (root["audit"] or {"axioms": {}})["axioms"].items():
            if set(axioms) - ALLOWED_AXIOMS:
                problems.append(f"{root_id}: {name} uses {axioms}")
    print("Recorded results are consistent with this tree." if not problems else f"PROBLEMS: {problems[:20]}")
    print("This is a cross-check of a recorded build, not a fresh verification.")
    return 0 if not problems else EXIT_FAILED


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("check", help="toolchain, manifest, closure, source scan, map generation")
    build = commands.add_parser("build", help="clean sequential build and axiom audit of the roots")
    build.add_argument("--build-dir", required=True)
    build.add_argument("--root", action="append", choices=sorted(ROOTS), help="restrict to these roots; repeatable")
    build.add_argument("--memory-mib", type=int, default=8192, help="lean -M limit per process")
    build.add_argument("--timeout-s", type=int, default=7200, help="wall limit per lean process")
    build.add_argument("--min-free-mib", type=int, default=400, help="stop cleanly below this much free disk")
    build.add_argument("--keep-oleans", action="store_true", help="never delete oleans; needs about 7 GiB")
    build.add_argument("--allow-dirty", action="store_true", help="development only; the receipt will not be PASS")
    receipt = commands.add_parser("receipt", help="write VERIFICATION_RECEIPT.json and receipts/")
    receipt.add_argument("--build-dir", required=True)
    commands.add_parser("check-receipt", help="cross-check recorded results against the tree; compiles nothing")
    args = parser.parse_args()
    args.argv = ["python3", "scripts/verify.py", *sys.argv[1:]]
    if args.command == "check":
        cmd_check()
        return 0
    return dict(build=cmd_build, receipt=cmd_receipt)[args.command](args) if args.command != "check-receipt" else cmd_check_receipt(args)


if __name__ == "__main__":
    sys.exit(main())
