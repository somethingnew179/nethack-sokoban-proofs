#!/usr/bin/env python3
"""Emit small ordinary-kernel run checks for one explicit full-map trace."""
import ast
import re
from diagnose import Model, HERE, REPO

def emit_witness(map_name, path, stem):
    model=Model(map_name)
    text=(REPO/'lean/NetHack/Sokoban/Maps.lean').read_text()
    text=text.split('def '+map_name+' : SourceMap :=')[1].split('\ntheorem ')[0]
    array=lambda key:ast.literal_eval(re.search(r'\b'+key+r' := (\[[^\]]*\])',text).group(1))
    boulders=array('boulders')
    holes=array('holes')
    state=model.initial
    lines=['import NetHack.Sokoban.Maps','set_option maxRecDepth 1000000',
           'set_option maxHeartbeats 0','namespace Owner1007.'+stem,'open NetHack.Sokoban']
    previous=map_name+'.initial'
    total=0
    chunks=[path[i:i+32] for i in range(0,len(path),32)]
    for i,chunk in enumerate(chunks):
        cost=0
        for direction in chunk:
            result=model.step(state,direction)
            assert result is not None, (i,direction,state)
            state,event=result
            if event:
                source,landing,filled=event
                boulders.remove(source)
                if filled is None:boulders.insert(0,landing)
                else:holes.remove(filled)
                cost+=1
        before=total
        total+=cost
        literal='{player := '+str(state[0])+', boulders := '+str(boulders)+', holes := '+str(holes)+'}'
        lines += [f'def block{i} : List Dir := ['+', '.join('.'+d for d in chunk)+']',
                  f'def state{i} : State := '+literal,
                  f'theorem checked{i} : run {map_name}.board {previous} block{i} = some ⟨state{i}, {cost}, {len(chunk)}⟩ := by decide +kernel']
        if i==0:
            lines += ['def prefix0 : List Dir := block0',
                      f'theorem prefix_checked0 : run {map_name}.board {map_name}.initial prefix0 = some ⟨state0, {total}, {len(chunk)}⟩ := checked0']
        else:
            lines += [f'def prefix{i} : List Dir := prefix{i-1} ++ block{i}',
                      f'theorem prefix_checked{i} : run {map_name}.board {map_name}.initial prefix{i} = some ⟨state{i}, {total}, {min(32*(i+1),len(path))}⟩ :=',
                      f'  run_append_of _ _ prefix{i-1} block{i} ⟨state{i-1}, {before}, {32*i}⟩ ⟨state{i}, {cost}, {len(chunk)}⟩ prefix_checked{i-1} checked{i}']
        previous=f'state{i}'
    assert not holes and not state[2]
    last=len(chunks)-1
    lines += [f'def path : List Dir := prefix{last}',f'def finalState : State := state{last}',
              f'theorem solution : Trace {map_name}.board {map_name}.initial path finalState {total} {len(path)} ∧ Goal finalState :=',
              f'  ⟨run_sound _ _ _ _ prefix_checked{last}, rfl⟩',
              '#print axioms solution','end Owner1007.'+stem]
    target=HERE/('Owner1007/'+stem+'.lean')
    target.write_text('\n'.join(lines)+'\n')
    return dict(pushes=total,moves=len(path),final_player=state[0],final_boulders=boulders,final_holes=holes,
                proof_source=str(target.relative_to(REPO)),kernel_checked=False)
