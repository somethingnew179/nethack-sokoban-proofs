#!/usr/bin/env python3
"""Prescribed custom-singleton diagnostic, never a canonical witness.
Uses original map, holes, rolling rule and walking BFS only; no configuration search.
Refutes an uncoupled singleton289 energy>=2 claim. OriginalReached is not supplied.
"""
import ast
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import sys
repo = Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path.cwd()
sim_path = repo/'research/owner1007/diagnose.py'
spec = importlib.util.spec_from_file_location('nethack_diagnostic_model',sim_path)
sim = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sim)
model = sim.Model('soko1_2')
potential_path = repo/'lean/NetHack/Sokoban/Generated/Soko12Potential.lean'
text = potential_path.read_text()
debt = ast.literal_eval(re.search(r'def soko1_2Debt : List Nat := (\[[^\]]*\])',text).group(1))
credit = ast.literal_eval(re.search(r'def soko1_2Credit : List Nat := (\[[^\]]*\])',text).group(1))
initial = (288,frozenset({289}),model.initial[2])
commands = [(289,'east'),(290,'east'),(291,'north'),(265,'north'),(239,'north'),(213,'west')]
commands += [(212-26*k,'north') for k in range(7)]
commands += [(30,'east')]
result = model.macros(initial,commands)
assert result is not None
final,path = result
state = initial
slacks = []
for direction in path:
    transition = model.step(state,direction)
    assert transition is not None
    state,event = transition
    if event:
        source,landing,filled = event
        slacks.append(1+debt[source]-(credit[filled] if filled is not None else debt[landing]))
assert state==final
assert len(slacks)==14 and all(value==0 for value in slacks)
assert not final[1] and len(final[2])==17
report = dict(
    scope='CUSTOM singleton289, hero288; original board/18 original holes; no OriginalReached; no original Goal',
    original_witness=False,
    refutes='Uncoupled singleton289 owned-energy>=2; does not refute any proved canonical bound',
    configuration_search=False, walking_bfs_only=True,
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    simulator_sha256=hashlib.sha256(sim_path.read_bytes()).hexdigest(),
    potential_sha256=hashlib.sha256(potential_path.read_bytes()).hexdigest(),
    initial=dict(hero=288,boulders=[289],holes=sorted(initial[2])),
    pushes=len(commands),moves=len(path),commands=commands,path=path,
    raw_step_slacks=slacks,owned_energy=sum(slacks)+sum(debt[c] for c in final[1]),
    final=dict(hero=final[0],boulders=sorted(final[1]),holes=sorted(final[2])),
    original_goal=False)
print(json.dumps(report,ensure_ascii=False,indent=2))
