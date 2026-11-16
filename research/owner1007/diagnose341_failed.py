#!/usr/bin/env python3
"""One explicit failed 341-push variant of checked342. No boulder-state search.
Walking connections alone use fixed-boulder BFS in diagnose.Model.macros.
Expected exit1: first317East has inaccessible support316 (hero369).
Run from assigned repository cwd with python3 -B.
"""
import sys,re
sys.path.insert(0,'research/owner1007')
from diagnose import Model
m=Model('soko1_1')
state=m.initial
labels={c:c for c in state[1]}
path,events=[],[]
def p(identity,code):
    global state
    for letter,count in re.findall(r'([NSEW])(\d+)',code):
        direction=dict(N='north',S='south',E='east',W='west')[letter]
        for _ in range(int(count)):
            source=labels[identity]
            old=state
            result=m.macros(state,[(source,direction)])
            if not result:
                print('FAILED',identity,code,'source',source,'nextdir',direction,
                      'hero',state[0],'boxes',sorted(state[1]))
                sys.exit(1)
            state,walked=result
            path.extend(walked)
            if len(state[2])<len(old[2]):
                del labels[identity]
            else:
                labels[identity]=next(iter(state[1]-(old[1]-{source})))
            events.append((identity,source,direction))
def deliver(identity):
    first=len(state[2])==16
    p(identity,'N3W1N3')
    if not first:
        p(identity,'E1')
for identity,code in [
    (264,'W1'),(293,'W1'),(367,'E3'),(317,'E2S3W4N1E1'),(293,'W2'),
    (186,'W2'),(268,'E2'),(266,'E1'),(212,'E1S3E2'),(188,'W2'),(191,'W2'),
    (139,'W1S3W3S3E1'),(137,'E1S3W3S3')]:
    p(identity,code)
for identity,code in [
    (191,'E1'),(188,'E4'),(186,'E6'),(193,'W3'),(137,'N4E3'),(266,'W2N3E3'),
    (212,'N1W2N3E3'),(139,'W1N4E3'),(264,'E2N3E3'),(268,'W5N3E3'),
    (293,'E1N4E3'),(367,'E1N4W2N3E3'),(317,'E3N4W2N3E3'),
    (135,'E3S3W3S3N4E3'),(133,'E5S3W3S3N4E3'),(141,'W3S3W3S3N4E3')]:
    p(identity,code)
    deliver(identity)
print('COMPLETE',not state[2],'PUSHES',len(events),'MOVES',len(path),'SURVIVORS',labels)
assert not state[2] and len(events)==341
