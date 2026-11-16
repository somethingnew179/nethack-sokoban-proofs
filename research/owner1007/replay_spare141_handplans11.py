#!/usr/bin/env python3
"""Prescribed changes to the342 witness: spare original141, deliver original321.
Only walking BFS; no search over boulder configurations or lower-bound claim.
"""
import json,re
from diagnose import Model,HERE

def trial(insertion):
 m=Model('soko1_1');state=m.initial;labels={c:c for c in state[1]};events=[];path=[]
 def p(identity,code):
  nonlocal state
  for letter,count in re.findall(r'([NSEW])(\d+)',code):
   direction=dict(N='north',S='south',E='east',W='west')[letter]
   for _ in range(int(count)):
    source=labels[identity];result=m.macros(state,[(source,direction)])
    if not result:
     support=m.adjacent(source,dict(north='south',south='north',east='west',west='east')[direction]);walks=m.walks(state)
     return dict(failed_identity=identity,failed_code=code,failed_command=[source,direction],support=support,support_reachable=support in walks,pushes=len(events),labels=labels)
    state,walked=result;target=m.adjacent(source,direction);filled=target not in state[1]
    if filled:del labels[identity]
    else:labels[identity]=target
    events.append(dict(identity=identity,source=source,direction=direction,landing=target,consumed=filled));path.extend(walked)
 def deliver(identity):
  first=len(state[2])==16
  failure=p(identity,'N3W1N3')
  return failure or (None if first else p(identity,'E1'))
 opening=[(264,'W1'),(293,'E1'),(321,'W1'),(367,'E3'),(317,'E2S3W4N1E1'),(186,'W2'),(268,'E2'),(266,'E1'),(212,'E1S3E2'),(188,'W2'),(191,'W2'),(139,'W1S3W3S3E1'),(137,'E1S3W3S3')]
 shipping=[(191,'E1'),(188,'E4'),(186,'E6'),(193,'W3'),(137,'N4E3'),(266,'W2N3E3'),(212,'N1W2N3E3'),(139,'W1N4E3'),(264,'E2N3E3'),(268,'W5N3E3'),(293,'W3N4E3'),(367,'E1N4W2N3E3'),(317,'E3N4W2N3E3'),(135,'E3S3W3S3N4E3'),(133,'E5S3W3S3N4E3')]
 for identity,code in opening:
  failure=p(identity,code)
  if failure:return dict(insertion=insertion,status='failed_prefix',failure=failure)
 for identity,code in shipping:
  failure=p(identity,code) or deliver(identity)
  if failure:return dict(insertion=insertion,status='failed_prefix',failure=failure)
  if identity==insertion:
   failure=p(321,'W1N2W2N3E3') or deliver(321)
   if failure:return dict(insertion=insertion,status='failed_321_delivery',failure=failure)
 return dict(insertion=insertion,status='goal' if not state[2] else 'incomplete',pushes=len(events),moves=len(path),remaining_holes=sorted(state[2]),final_identities=labels,path=path,events=events)

def main():
 reports=[trial(identity) for identity in [212,139,264,268]]
 report=dict(map='soko1-1',original_canonical_start=True,boulder_configuration_search=False,method='Exactly four prescribed schedules based on342 witness; walking BFS only',scope='Python diagnostics; any successful candidate still requires Lean kernel witness',cases=reports)
 (HERE/'spare141_handplans11_diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
 for r in reports:print(r['insertion'],r['status'],r.get('pushes'),r.get('failure'))
if __name__=='__main__':main()
