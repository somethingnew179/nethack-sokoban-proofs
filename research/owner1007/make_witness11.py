#!/usr/bin/env python3
"""A hand-planned parking change, walking BFS only; emits a Lean proposal."""
import json
import argparse
from diagnose import Model, HERE

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--short293", action="store_true")
    args = parser.parse_args()
    model = Model("soko1_1")
    state = model.initial
    labels = {c:c for c in state[1]}
    path, commands = [], []
    def push(identity, direction, count=1):
        nonlocal state
        for _ in range(count):
            source = labels[identity]
            result = model.macros(state, [(source,direction)])
            assert result, (identity, direction, source, state)
            after, walked = result
            actor = model.adjacent(source, {"north":"south","south":"north","east":"west","west":"east"}[direction])
            check = model.step((actor,state[1],state[2]),direction)
            assert check and check[1]
            _,landing,filled = check[1]
            if filled is not None:
                del labels[identity]
            else:
                labels[identity] = landing
            commands.append([identity,source,direction,landing,filled])
            path.extend(walked)
            state = after
    def p(identity, text):
        for d,n in text:
            push(identity,d,n)
    def deliver(identity):
        first = len(state[2]) == 16
        p(identity,[("north",3),("west",1),("north",3)])
        if not first:
            push(identity,"east")
    p(264,[("west",1)])
    p(293,[("east",1 if args.short293 else 3)])
    if args.short293:
        push(321,"east")
    p(367,[("east",3)])
    p(317,[("east",2),("south",3),("west",4),("north",1),("east",1)])
    p(186,[("west",2)])
    p(212,[("east",1),("south",4),("east",2),("south",3),("west",5),("north",1)])
    p(188,[("west",2)])
    p(191,[("west",2)])
    p(139,[("west",1),("south",3),("west",3),("south",3),("east",1)])
    p(137,[("east",1),("south",3),("west",3),("south",3)])
    for identity,shift in [(191,1),(188,4),(186,6)]:
        push(identity,"east",shift); deliver(identity)
    push(193,"west",3); deliver(193)
    p(137,[("north",4),("east",3)]); deliver(137)
    p(139,[("west",1),("north",4),("east",3)]); deliver(139)
    for identity,shift in [(264,2),(266,-1),(268,-3),(293,-3 if args.short293 else -5)]:
        p(identity,[("east" if shift>0 else "west",abs(shift)),("north",4 if identity==293 else 3),("east",3)])
        deliver(identity)
    for identity,shift in [(367,1),(317,3),(212,5)]:
        p(identity,[("east",shift),("north",4),("west",2),("north",3),("east",3)])
        deliver(identity)
    for identity,shift in [(135,3),(133,5),(141,-3)]:
        p(identity,[("east" if shift>0 else "west",abs(shift)),("south",3),("west",3),("south",3),("north",4),("east",3)])
        deliver(identity)
    count, moves = len(commands), len(path)
    assert count == (354 if args.short293 else 357) and not state[2], (count,moves,state)
    stem = "Witness11_354" if args.short293 else "Witness11"
    (HERE / f"witness11_{count}.json").write_text(json.dumps(dict(pushes=count,moves=moves,path=path,commands=commands,final=[state[0],sorted(state[1]),sorted(state[2])]),indent=2)+"\n")

    # Lists in Model.lean are ordered: reconstruct them exactly, not as sets.
    boulders = [133,135,137,139,141,186,212,188,191,193,315,264,317,266,293,268,321,367]
    holes = [33,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
    state = model.initial
    def literal(player):
        return "{player := "+str(player)+", boulders := "+str(boulders)+", holes := "+str(holes)+"}"
    lines = ["import NetHack.Sokoban.Maps", "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "namespace Owner1007."+stem, "open NetHack.Sokoban"]
    previous = "soko1_1.initial"
    total = 0
    chunks = [path[i:i+32] for i in range(0,len(path),32)]
    for i,chunk in enumerate(chunks):
        cost=0
        for d in chunk:
            result=model.step(state,d)
            assert result
            state,event=result
            if event:
                source,landing,filled=event
                boulders.remove(source)
                if filled is None:boulders.insert(0,landing)
                else:holes.remove(filled)
                cost+=1
        total+=cost
        lines += [f"def block{i} : List Dir := ["+", ".join("."+d for d in chunk)+"]",
                  f"def state{i} : State := "+literal(state[0]),
                  f"theorem checked{i} : run soko1_1.board {previous} block{i} = some ⟨state{i}, {cost}, {len(chunk)}⟩ := by decide +kernel"]
        if i==0:
            lines += ["def prefix0 : List Dir := block0", f"theorem prefix_checked0 : run soko1_1.board soko1_1.initial prefix0 = some ⟨state0, {total}, {len(chunk)}⟩ := checked0"]
        else:
            prev_total = total-cost
            lines += [f"def prefix{i} : List Dir := prefix{i-1} ++ block{i}",
                      f"theorem prefix_checked{i} : run soko1_1.board soko1_1.initial prefix{i} = some ⟨state{i}, {total}, {min(32*(i+1),len(path))}⟩ :=",
                      f"  run_append_of _ _ prefix{i-1} block{i} ⟨state{i-1}, {prev_total}, {32*i}⟩ ⟨state{i}, {cost}, {len(chunk)}⟩ prefix_checked{i-1} checked{i}"]
        previous = f"state{i}"
    last=len(chunks)-1
    lines += [f"def path : List Dir := prefix{last}", f"def finalState : State := state{last}",
              f"theorem solution : Trace soko1_1.board soko1_1.initial path finalState {count} {moves} ∧ Goal finalState :=",
              f"  ⟨run_sound _ _ _ _ prefix_checked{last}, rfl⟩", "#print axioms solution", "end Owner1007."+stem]
    (HERE / ("Owner1007/"+stem+".lean")).write_text("\n".join(lines)+"\n")
    print(f"explicit candidate: {count} pushes, {moves} moves; Lean proposal generated, not yet a proof")

if __name__=="__main__":main()
