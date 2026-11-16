#!/usr/bin/env python3
"""Prescribed H7 ghost queue attaining owned energy4; no state search.
CUSTOM seven-token start, original board and18holes. Not canonical and NOT Goal.
"""
import ast, hashlib, importlib.util, json, pathlib, re
REPO=pathlib.Path("/Users/ilyakondakov/PycharmProjects/myagent/local/bot-artifacts/nethack-invariants-owner1007/repo")
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("owner1007_diag",REPO/"research/owner1007/diagnose.py")
diag=importlib.util.module_from_spec(spec);spec.loader.exec_module(diag)
model=diag.Model("soko1_2")
potential=REPO/"lean/NetHack/Sokoban/Generated/Soko12Potential.lean"
debt=ast.literal_eval(re.search(r"def soko1_2Debt : List Nat := (\[[^\]]*\])",potential.read_text()).group(1))
commands=[[238,"west"],[158,"north"],[159,"east"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[187,"south"],[186,"west"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[132,"east"],[133,"east"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[185,"north"],[159,"north"],[133,"east"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[212,"north"],[186,"north"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[213,"west"],[212,"north"],[186,"north"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[237,"north"],[211,"north"],[185,"north"],[159,"north"],[133,"east"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"]]
boxes=frozenset([108,158,159,186,187,212,238])
initial=(265,boxes,model.initial[2])
done=model.macros(initial,commands)
assert done is not None
final,path=done
energy=len(commands)+sum(debt[c] for c in boxes)-18*(len(initial[2])-len(final[2]))
assert (len(commands),len(path),energy,len(final[1]),len(final[2]))==(57,137,4,0,11)
# Retaining original237 immediately blocks the queue's first238West target.
h8=(265,boxes|{237},model.initial[2])
assert model.macros(h8,[commands[0]]) is None
sources=[pathlib.Path(__file__),REPO/"research/owner1007/diagnose.py",REPO/"lean/NetHack/Sokoban/Maps.lean",potential]
report=dict(scope="CUSTOM H7 relaxation, hero265 and seven stonesU5+[212238], original18holes; consumes7stones but leaves11holes. NOT originalcanonical Goal/witness/upperbound.",
 method="One manually prescribed57-push queue with walkingBFS replay; no boulder configuration search.",
 initial=dict(hero=initial[0],boulders=sorted(boxes),holes=sorted(initial[2])),
 commands=commands,path=path,pushes=len(commands),moves=len(path),owned_energy=energy,
 final=dict(hero=final[0],boulders=sorted(final[1]),holes=sorted(final[2])),
 retained237=dict(scope="One additional original stone237; same queue fails immediately at238West",first_command=commands[0],legal=False),
 source_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
output=HERE/"joint_h7_sharp4.json";output.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(dict(output=str(output),pushes=len(commands),moves=len(path),owned_energy=energy,remaining_holes=len(final[2]),with237_first_command_legal=False)))
