#!/usr/bin/env python3
"""Replay packaged witnesses and test local deletions; no boulder-state search."""
import ast
from collections import deque
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
DIRS = dict(north=(0,-1), south=(0,1), east=(1,0), west=(-1,0),
            northEast=(1,-1), northWest=(-1,-1), southEast=(1,1), southWest=(-1,1))

class Model:
    def __init__(self, name):
        self.name = name
        text = (REPO / "lean/NetHack/Sokoban/Maps.lean").read_text()
        text = text.split("def " + name + " : SourceMap :=")[1].split("\ntheorem ")[0]
        array = lambda k: ast.literal_eval(re.search(r"\b"+k+r" := (\[[^\]]*\])", text).group(1))
        self.w = int(re.search(r"width := (\d+)", text).group(1))
        self.h = int(re.search(r"height := (\d+)", text).group(1))
        self.floor, self.doors, self.traps = map(set, [array("floor"), array("doors"), array("rollingTraps")])
        self.initial = (int(re.search(r"player := (\d+)", text).group(1)), frozenset(array("boulders")), frozenset(array("holes")))

    def adjacent(self, c, d):
        dx,dy = DIRS[d]
        x,y = c%self.w+dx, c//self.w+dy
        return x+self.w*y if 0 <= x < self.w and 0 <= y < self.h else None

    def step(self, state, d):
        hero, boxes, holes = state
        if not holes or hero not in self.floor or hero in self.doors|boxes|holes:
            return None
        tar = self.adjacent(hero,d)
        if tar not in self.floor or tar in self.doors:
            return None
        dx,dy = DIRS[d]
        if dx and dy:
            sides = [self.adjacent(hero, "east" if dx>0 else "west"), self.adjacent(hero,"south" if dy>0 else "north")]
            if all((c not in self.floor and c not in self.doors) or c in boxes for c in sides):
                return None
        if tar not in boxes:
            return None if tar in holes else ((tar, boxes, holes), None)
        if dx and dy:
            return None
        dest = self.adjacent(tar,d)
        if dest not in self.floor or dest in self.doors|boxes:
            return None
        stationary = boxes - {tar}
        landing, filled = dest, None
        if dest in holes:
            filled = dest
        elif dest in self.traps:
            landing = tar
            for _ in range(self.w*self.h+1):
                nxt = self.adjacent(landing,d)
                if nxt in self.doors:
                    return None
                if nxt not in self.floor:
                    break
                if nxt in stationary:
                    return None
                landing = nxt
                if nxt in holes:
                    filled = nxt
                    break
            else:
                return None
        after = (tar, frozenset(stationary if filled is not None else stationary|{landing}), frozenset(holes-{filled}))
        return after, (tar, landing, filled)

    def walks(self, state):
        hero,boxes,holes = state
        paths, queue = {hero: []}, deque([hero])
        while queue:
            c = queue.popleft()
            for d in DIRS:
                result = self.step((c,boxes,holes),d)
                if result and result[1] is None and result[0][0] not in paths:
                    target = result[0][0]
                    paths[target] = paths[c]+[d]
                    queue.append(target)
        return paths

    def macros(self, state, commands):
        path = []
        for source,d in commands:
            behind = self.adjacent(source, dict(north="south",south="north",east="west",west="east")[d])
            walks = self.walks(state)
            if behind not in walks:
                return None
            path += walks[behind]+[d]
            result = self.step((behind,state[1],state[2]),d)
            if not result or not result[1] or result[1][0] != source:
                return None
            state = result[0]
        return state,path

def witness(tag):
    blocks = sorted((REPO / "lean/NetHack/Sokoban/Generated").glob("Soko"+tag+"Macro*Blocks*.lean"))
    paths = []
    for file in blocks:
        for body in re.findall(r"def soko\d_\dMacro\w+Block\d+ : List Dir := \[([^\]]*)\]",file.read_text()):
            paths += re.findall(r"\.([A-Za-z]+)",body)
    return paths

def replay(model, path):
    state = model.initial
    states, commands, events = [state], [], []
    labels = {c:c for c in state[1]}
    for i,d in enumerate(path):
        result = model.step(state,d)
        assert result is not None, (model.name,i,d,state)
        state,event = result
        if event:
            source,landing,filled = event
            identity = labels.pop(source)
            if filled is None:
                labels[landing] = identity
            commands.append((source,d))
            events.append(dict(move=i+1,push=len(commands),identity=identity,source=source,landing=landing,filled=filled))
            states.append(state)
    assert not state[2]
    return states,commands,events,labels

def local_deletions(model, commands):
    """Only O(n^2) replay of the SAME command list minus 1 or 2 adjacent pushes."""
    found = []
    for size in (1,2):
        for i in range(len(commands)-size+1):
            result = model.macros(model.initial,commands[:i]+commands[i+size:])
            if result and not result[0][2]:
                found.append(dict(start=i+1,removed=size,pushes=len(commands)-size,path=result[1]))
    return found

def main():
    reports = {}
    for tag,name,expected in [("11","soko1_1",(375,778)),("12","soko1_2",(235,578)),("32","soko3_2",(147,764))]:
        m = Model(name)
        path = witness(tag)
        states,commands,events,labels = replay(m,path)
        assert (len(commands),len(path)) == expected
        reconstructed = m.macros(m.initial,commands)
        assert reconstructed and reconstructed[0] == states[-1]
        findings = local_deletions(m,commands)
        reports[name] = dict(pushes=len(commands),moves=len(path),survivor_labels=labels,events=events,
                             local_deletion_trials=2*len(commands)-1,local_improvements=findings)
        print(name, "replay",expected,"survivors",labels,"local_improvements",len(findings),flush=True)
    (HERE / "witness_diagnostics.json").write_text(json.dumps(reports,indent=2)+"\n")

if __name__ == "__main__":
    main()
