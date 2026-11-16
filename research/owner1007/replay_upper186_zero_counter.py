#!/usr/bin/env python3
"""Prescribed local counter to uncoupled Upper4 after zero186North160.
CUSTOM5tokens and13remainingholes. No canonical Goal or upper-bound claim.
"""
import ast,hashlib,importlib.util,json,pathlib,re
REPO=pathlib.Path("/Users/ilyakondakov/PycharmProjects/myagent/local/bot-artifacts/nethack-invariants-owner1007/repo")
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("owner1007_diag",REPO/"research/owner1007/diagnose.py")
diag=importlib.util.module_from_spec(spec);spec.loader.exec_module(diag);model=diag.Model("soko1_2")
potential=REPO/"lean/NetHack/Sokoban/Generated/Soko12Potential.lean"
debt=ast.literal_eval(re.search(r"def soko1_2Debt : List Nat := (\[[^\]]*\])",potential.read_text()).group(1))
commands=[[158,"north"],[132,"south"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[187,"south"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[158,"north"],[159,"east"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[132,"east"],[133,"east"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"],[213,"west"],[212,"north"],[186,"north"],[160,"north"],[134,"north"],[108,"north"],[82,"north"],[56,"north"],[30,"east"]]
boxes=frozenset([108,158,159,160,187]);initial=(186,boxes,model.initial[2])
done=model.macros(initial,commands);assert done is not None
final,path=done;energy=len(commands)+sum(debt[c] for c in boxes)-18*(18-len(final[2]))
assert(len(commands),len(path),energy,len(final[1]),len(final[2]))==(37,94,2,0,13)
sources=[pathlib.Path(__file__),REPO/"research/owner1007/diagnose.py",REPO/"lean/NetHack/Sokoban/Maps.lean",potential]
report=dict(scope="CUSTOMfive-token stateUpper[108158159160187],hero186; originalboard/rules/18holes; allfiveconsume13holesremain. NOTcanonicalGoal/witness/upperbound.",
 refutes="Uncoupled futureUpperenergy>=4 afterzero186North160; originalCore/S barriers are omitted in this relaxation.",
 method="One prescribed37-push queue, exactreplay+walkingBFSonly; noboulder-state search.",
 initial=dict(hero=initial[0],boulders=sorted(boxes),holes=sorted(initial[2])),
 commands=commands,path=path,pushes=len(commands),moves=len(path),owned_energy=energy,
 final=dict(hero=final[0],boulders=sorted(final[1]),holes=sorted(final[2])),
 source_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
out=HERE/"upper186_zero_counter.json";out.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(dict(output=str(out),pushes=len(commands),moves=len(path),owned_energy=energy,remaining_holes=len(final[2]))))
