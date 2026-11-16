#!/usr/bin/env python3
"""Prescribed original-state partial trace for the rejected cheap E-first Upper plan.
Walking BFS only, no configuration search. This is not a winning witness.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
repo=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path.cwd()
model_path=repo/'research/owner1007/diagnose.py'
spec=importlib.util.spec_from_file_location('nethack_model',model_path)
sim=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sim)
model=sim.Model('soko1_2')
commands=[
 (371,'east'),(372,'east'),(373,'east'),(374,'north'),(348,'north'),(322,'north'),(296,'north'),
 (271,'north'),(246,'north'),(220,'north'),(193,'north'),
 (192,'west'),(191,'west'),(190,'west'),
 (210,'north'),(213,'east'),(186,'north'),(159,'north'),(160,'north')]
result=model.macros(model.initial,commands)
assert result is not None
state,path=result
assert all(cell in state[1] for cell in (108,133,134))
assert len(state[2])==18
report=dict(scope='FULL canonical original soko1_2 state; prescribed partial trace, no original Goal/winning claim',
 configuration_search=False,walking_bfs_only=True,
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 simulator_sha256=hashlib.sha256(model_path.read_bytes()).hexdigest(),
 commands=commands,path=path,pushes=len(commands),moves=len(path),
 final=dict(hero=state[0],boulders=sorted(state[1]),holes=sorted(state[2])),
 locked_cells=[108,133,134],
 interpretation='Rejects this ordering of the E-first Core210North/S213East Upper plan; the three retained stones form a permanent lock',
 validation='Python original-model replay only for the partial trace; separate Upper133134Dead12.lean proves that any original-reached state containing these cells cannot complete',
 original_goal=False,winning_witness=False)
print(json.dumps(report,indent=2))
