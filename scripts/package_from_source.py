#!/usr/bin/env python3
"""How this repository's proof tree was derived from the read-only source checkout.

Copies, byte for byte and at the same relative path, the import closure of the
audit roots plus the map inputs and generators. The source is only read; `cp -c`
makes an APFS clone where possible and falls back to a plain copy. Then rewrites
MANIFEST.sha256 from everything tracked or about to be tracked.

  python3 scripts/package_from_source.py --source <NetHack checkout with lean/>

Running it is only needed to re-derive the tree; verification does not use it.
"""
from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify  # noqa: E402

COPIED_FILES = [
    "dat/license",
    *[f"dat/soko{floor}-{variant}.lua" for floor in range(1, 5) for variant in (1, 2)],
    "docs/SOKOBAN_SOURCE_AUDIT_20261030_RU.md",
    "docs/SOKOBAN_PATH_SOURCE_SAFETY_20261030_RU.md",
    "lean/lean-toolchain",
    "lean/lake-manifest.json",
    "lean/validation/sokoban/model/README.md",
    "lean/validation/sokoban/source/extract.py",
    "lean/validation/sokoban/source/generate_lean.py",
    "lean/validation/sokoban/source/maps.json",
]
AUTHORED_TOP_LEVEL = ["roots.json", "LICENSE", "NOTICE.md", ".gitignore", ".gitattributes", "scripts/verify.py", "scripts/package_from_source.py", "lean/lakefile.toml"]


def clone_or_copy(source: Path, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    if subprocess.run(["cp", "-c", str(source), str(target)], capture_output=True).returncode:
        shutil.copyfile(source, target)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source", required=True, type=Path)
    source_root = parser.parse_args().source.resolve()

    def resolve(module: str) -> Path:
        if module.startswith("Audit."):
            return verify.source_path(module)
        return source_root / "lean" / (module.replace(".", "/") + ".lean")

    graph = verify.ImportGraph(resolve)
    union: set[str] = set()
    for root_id in verify.ROOTS:
        union |= graph.closure(graph.imports(verify.ROOTS[root_id]["audit_module"]))
    for module in sorted(union):
        relative = Path("lean") / (module.replace(".", "/") + ".lean")
        target = verify.REPO / relative
        if not target.exists():
            clone_or_copy(source_root / relative, target)
    for relative in COPIED_FILES:
        target = verify.REPO / relative
        if not target.exists():
            clone_or_copy(source_root / relative, target)

    covered = [p for p in COPIED_FILES + AUTHORED_TOP_LEVEL]
    covered += [str(p.relative_to(verify.REPO)) for p in (verify.REPO / "lean").rglob("*.lean")]
    lines = []
    for relative in sorted(set(covered)):
        digest = hashlib.sha256((verify.REPO / relative).read_bytes()).hexdigest()
        lines.append(f"{digest}  {relative}")
    verify.MANIFEST.write_text("\n".join(lines) + "\n")
    print(f"closure modules: {len(union)}; manifest entries: {len(lines)}; external imports: {sorted(graph.external)}")


if __name__ == "__main__":
    main()
