#!/usr/bin/env python3
"""Two prescribed local pipe queues; walking BFS only, no puzzle-state search.
Scope: CUSTOM three-token state, original board and 18 original holes.
Neither queue is an original canonical solution or a Goal witness.
"""
import ast, hashlib, importlib.util, json, pathlib, re
REPO=pathlib.Path("/Users/ilyakondakov/PycharmProjects/myagent/local/bot-artifacts/nethack-invariants-owner1007/repo")
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("owner1007_diag", REPO/"research/owner1007/diagnose.py")
diag=importlib.util.module_from_spec(spec);spec.loader.exec_module(diag)
model=diag.Model("soko1_2")
potential=REPO/"lean/NetHack/Sokoban/Generated/Soko12Potential.lean"
debt=ast.literal_eval(re.search(r"def soko1_2Debt : List Nat := (\[[^\]]*\])",potential.read_text()).group(1))
initial=(319,frozenset([320,292,345]),model.initial[2])
deliver=[(291,"north"),(265,"north"),(239,"north"),(213,"west")]+[(c,"north") for c in [212,186,160,134,108,82,56]]+[(30,"east")]
queues={
 "leave_371_at345":[(292,"west")]+deliver,
 "open_right_with_371_at293":[(292,"west"),(291,"north"),(345,"north"),(319,"north")]+deliver[1:]+[(293,"west")],
}
result={}
for name,commands in queues.items():
 state=initial;path=[];events=[];slack=0;failed=None
 for k,(source,direction) in enumerate(commands):
  before=state;done=model.macros(state,[(source,direction)])
  if done is None:
   behind=model.adjacent(source,dict(north="south",south="north",east="west",west="east")[direction])
   failed=dict(command_index=k+1,command=[source,direction],required_support=behind,hero=state[0],boulders=sorted(state[1]),holes=len(state[2]),reachable=sorted(model.walks(state)))
   break
  state,walk=done;path+=walk
  moved=list(state[1]-before[1]);filled=sorted(before[2]-state[2])
  one=1+debt[source]-(18 if filled else debt[moved[0]])
  slack+=one
  events.append(dict(command_index=k+1,source=source,direction=direction,landing=(filled[0] if filled else moved[0]),filled=filled,scalar_slack=one))
 result[name]=dict(commands=commands,successful_pushes=len(events),moves=len(path),events=events,prefix_slack=slack,failed=failed,final_hero=state[0],final_boulders=sorted(state[1]),remaining_holes=len(state[2]),path=path)
 assert failed is not None
assert result["leave_371_at345"]["failed"]["command"]==[213,"west"]
assert result["leave_371_at345"]["events"][0]["scalar_slack"]==0
assert result["open_right_with_371_at293"]["failed"]["command"]==[293,"west"]
assert result["open_right_with_371_at293"]["remaining_holes"]==17
sources=[pathlib.Path(__file__),REPO/"research/owner1007/diagnose.py",REPO/"lean/NetHack/Sokoban/Maps.lean",potential]
report=dict(scope="CUSTOM three-token partial-hole diagnostics; not an original canonical Goal witness",method="Two manually prescribed queues; replay plus walking BFS only, no boulder configuration search",initial=dict(hero=initial[0],boulders=sorted(initial[1]),holes=sorted(initial[2])),source_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},results=result)
output=HERE/"corner320_failed_queues.json";output.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(dict(output=str(output),results={k:dict(pushes=v["successful_pushes"],moves=v["moves"],slack=v["prefix_slack"],failure=v["failed"]["command"],support=v["failed"]["required_support"],remaining_holes=v["remaining_holes"]) for k,v in result.items()}),ensure_ascii=False))
