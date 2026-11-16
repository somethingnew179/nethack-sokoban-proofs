#!/usr/bin/env python3
"""A prescribed structural push plan, with walking routes only supplied by BFS."""
import json
from diagnose import Model,HERE,replay
from emit_witness import emit_witness

def main():
    delta={'N':-26,'S':26,'E':1,'W':-1}
    names={'N':'north','S':'south','E':'east','W':'west'}
    plan=[]
    def add(source,*directions):
        for direction in directions:
            plan.append((source,names[direction]))
            source+=delta[direction]
    def deliver(source):
        if source==189:add(189,'S');source=215
        if source==135:add(135,'E');source=136
        if source==136:add(136,'S');source=162
        if source==159:add(159,'E','E','E');source=162
        if source==162:add(162,'S');source=188
        if source==188:add(188,'S');source=214
        if source==214:add(214,'E');source=215
        if source==215:add(215,'S');source=241
        if source==241:add(241,'S');source=267
        if source==267:add(267,'S');source=293
        if source==289:add(289,'E','E');source=291
        if source==291:add(291,'E','E');source=293
        if source==293:add(293,'E','E');source=295
        if source==295:add(295,'N','N');source=243
        if source==243:add(243,'E');source=244
        if source==244:add(244,'S');source=270
        assert source==270
        add(270,'E')
    add(158,'E');add(132,'N');add(134,'E')
    add(86,'S','S');add(113,'E')
    add(211,'E','E','E')
    add(239,'S','S')
    add(267,'S');add(215,'S','S')
    add(293,'E','E');add(270,'E');add(244,'W');add(139,'N');add(138,'W')
    deliver(243);deliver(295);deliver(267)
    deliver(214);deliver(188)
    add(137,'W');deliver(136)
    deliver(135)
    add(161,'E');deliver(162)
    deliver(159)
    add(291,'N')
    deliver(289)
    add(265,'S');deliver(291)
    assert len(plan)==141
    model=Model('soko3_2')
    result=model.macros(model.initial,plan)
    assert result is not None
    final,path=result
    assert len(path)==610 and not final[2] and final[1]=={80,106,113,114}
    _,_,events,labels=replay(model,path)
    proposal=emit_witness('soko3_2',path,'Witness32_141')
    proposal.update(path=path,commands=plan,events=events,surviving_identities=labels,
        method='prescribed push schedule; shortest WALK routes only; no boulder-state search')
    (HERE/'witness32_141.json').write_text(json.dumps(proposal,indent=2)+'\n')
    print('Explicit141-push/610-move candidate generated; Lean check required')

if __name__=='__main__':main()
