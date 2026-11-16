#!/usr/bin/env python3
"""Replay one prescribed seven-token diagnostic; no puzzle-state search."""
import argparse, ast, hashlib, json, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
p=argparse.ArgumentParser()
p.add_argument("--repo",required=True)
p.add_argument("--data",default=str(Path(__file__).with_name("ghost_g4_diagnostic.json")))
args=p.parse_args()
repo=Path(args.repo).resolve()
sys.path.insert(0,str(repo/"research/owner1007"))
from diagnose import Model
data=json.loads(Path(args.data).read_text())
m=Model("soko1_2")
st=(371,frozenset(data["initial_boulders"]),m.initial[2])
pushes=0
for index,direction in enumerate(data["path"],1):
    result=m.step(st,direction)
    assert result is not None,(index,direction,st)
    st,event=result
    pushes+=event is not None
assert pushes==87 and len(data["path"])==246
assert len(st[2])==11 and not st[1]
source=(repo/"lean/NetHack/Sokoban/Generated/Soko12Potential.lean").read_text()
debt=ast.literal_eval(re.search(r"def soko1_2Debt : List Nat := (\[[^\n]*\])",source).group(1))
initial_debt=sum(debt[c] for c in data["initial_boulders"])
assert initial_debt==43
energy=initial_debt+pushes-(18-len(st[2]))*18
assert energy==4
print(json.dumps(dict(scope=data["scope"],pushes=pushes,moves=len(data["path"]),energy=energy,
    remaining_holes=len(st[2]),remaining_boulders=len(st[1]),original_goal=False),ensure_ascii=False))
