#!/usr/bin/env python3
"""Fourteen supplied access phases; BFS only over walking cells with fixed locks."""
from collections import deque
from diagnose import HERE,Model,DIRS
import json

U=[108,158,159,186,187]
J=[210,237,238,263,265,318]
N=[(J+[c]+U+[s],371,c,s) for c in [345,319,293,292,291] for s in [213,212]]
R=[([210,237,238,263,290]+U+[s,t],291,t,s) for t in [265,239] for s in [213,212]]

def walking(model,locks,seed):
    occupied=set(locks);seen={seed};queue=deque([seed])
    while queue:
        hero=queue.popleft()
        for direction,(dx,dy) in DIRS.items():
            target=model.adjacent(hero,direction)
            if target not in model.floor or target in model.doors or target in occupied:continue
            if dx and dy:
                sides=[model.adjacent(hero,'east' if dx>0 else 'west'),model.adjacent(hero,'south' if dy>0 else 'north')]
                if all(c not in model.floor or c in occupied for c in sides):continue
            if target not in seen:seen.add(target);queue.append(target)
    return sorted(seen)

def literal(x):return str(x).replace(' ','')

def main():
    model=Model('soko1_2');p=HERE/'Owner1007'
    data='''import Owner1007.FastCorral11
import Owner1007.NorthEvents12
import Owner1007.RingCut12
namespace Owner1007.PreCage12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
def U : List Cell := [108,158,159,186,187]
def sPaid (source : Cell) (dir : Dir) : Prop := (source=213 ∧ dir≠.west) ∨ source=212
instance (source : Cell) (dir : Dir) : Decidable (sPaid source dir) := by unfold sPaid; infer_instance
'''
    rows={}
    for name,family in [('north',N),('ring',R)]:
        n=len(family);regions=[walking(model,k,seed) for k,seed,_,_ in family]
        rows[name]=[dict(locks=k,seed=seed,tag=t,s=s,region=r) for (k,seed,t,s),r in zip(family,regions)]
        data+=f'''def {name}Patterns : List (List Cell) := {literal([a[0] for a in family])}
def {name}Locks (i : Fin {n}) : List Cell := {name}Patterns[i.val]?.getD []
def {name}Regions : List (List Cell) := {literal(regions)}
def {name}Region (i : Fin {n}) : List Cell := {name}Regions[i.val]?.getD []
def {name}S (i : Fin {n}) : Cell := {literal([a[3] for a in family])}[i.val]?.getD 0
def {name}Tag (i : Fin {n}) : Cell := {literal([a[2] for a in family])}[i.val]?.getD 0
'''
    data+='''def northPaid (source : Cell) (dir : Dir) : Prop :=
 NorthEvents12.paid source dir ∨ source∈U ∨ sPaid source dir
def ringPaid (source : Cell) (dir : Dir) : Prop :=
 RingCut12.paid source dir ∨ source∈U ∨ sPaid source dir ∨
 source=239 ∨ (source=265 ∧ dir=.south) ∨ (source=238 ∧ dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (northPaid source dir) := by unfold northPaid; infer_instance
instance (source : Cell) (dir : Dir) : Decidable (ringPaid source dir) := by unfold ringPaid; infer_instance

def northAllowed (i : Fin 10) (source : Cell) (dir : Dir) (j : Fin 10) (dest : Cell) : Prop :=
 (northS i=213 ∧ source=213 ∧ dir=.west ∧ j.val=i.val+1 ∧ dest=212) ∨
 (j.val=i.val+2 ∧ source=northTag i ∧
   ((source=345 ∧ dir=.north ∧ dest=319) ∨ (source=319 ∧ dir=.north ∧ dest=293) ∨
    (source=293 ∧ dir=.west ∧ dest=292) ∨ (source=292 ∧ dir=.west ∧ dest=291)))
def ringAllowed (i : Fin 4) (source : Cell) (dir : Dir) (j : Fin 4) (dest : Cell) : Prop :=
 (ringS i=213 ∧ source=213 ∧ dir=.west ∧ j.val=i.val+1 ∧ dest=212) ∨
 (ringTag i=265 ∧ source=265 ∧ dir=.north ∧ j.val=i.val+2 ∧ dest=239)
instance (i source dir j dest) : Decidable (northAllowed i source dir j dest) := by unfold northAllowed; infer_instance
instance (i source dir j dest) : Decidable (ringAllowed i source dir j dest) := by unfold ringAllowed; infer_instance

def TaggedShift {n : Nat} (locks region : Fin n → List Cell)
 (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop) (i : Fin n) (source : Cell) (dir : Dir) : Prop :=
 ∃ j : Fin n, ∃ dest∈pushTargets soko1_2.board source dir,
 pushTargets soko1_2.board source dir=[dest] ∧ dest∉soko1_2.initial.holes ∧
 locks j⊆dest::(locks i).erase source ∧ source∈region j ∧ allowed i source dir j dest
instance {n} (locks region : Fin n → List Cell) (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop)
 [∀ i source dir j dest, Decidable (allowed i source dir j dest)] (i source dir) :
 Decidable (TaggedShift locks region allowed i source dir) := by unfold TaggedShift; infer_instance

def tagPart {n : Nat} (locks region : Fin n → List Cell) (paid : Cell → Dir → Prop)
 (allowed : Fin n → Cell → Dir → Fin n → Cell → Prop)
 [∀ source dir, Decidable (paid source dir)] [∀ i source dir j dest, Decidable (allowed i source dir j dest)]
 (i : Fin n) : Bool :=
 (locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_2.board source dir.opposite with
 | none => true
 | some hero => if hero∈region i then
   decide (BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨ TaggedShift locks region allowed i source dir)
   else true
end Owner1007.PreCage12
'''
    (p/'PreCage12Data.lean').write_text(data)
    imports=[]
    for name,family in [('north',N),('ring',R)]:
        for i in range(len(family)):
            module=f'PreCage12{name.title()}{i}';imports.append(module)
            code='import Owner1007.PreCage12Data\nnamespace Owner1007.PreCage12\nopen NetHack.Sokoban\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
            for d in DIRS:
                code+=f'theorem {name}{i}_{d} : FastCorral11.walkPart soko1_2.board {name}Locks {name}Region {i} .{d}=true := by decide +kernel\n'
            code+=f'theorem {name}{i}_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes {name}Locks {name}Region {name}Paid {i}=true := by decide +kernel\n'
            code+=f'theorem {name}{i}_tags : tagPart {name}Locks {name}Region {name}Paid {name}Allowed {i}=true := by decide +kernel\n'
            code+=f'theorem {name}{i} : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes {name}Locks {name}Region {name}Paid {i}=true := by\n apply FastCorral11.node_of_parts\n · intro dir\n   cases dir with\n'
            code+=''.join(f'   | {d} => exact {name}{i}_{d}\n' for d in DIRS)
            code+=f' · exact {name}{i}_push\n#print axioms {name}{i}\n#print axioms {name}{i}_tags\nend Owner1007.PreCage12\n'
            (p/(module+'.lean')).write_text(code)
    root=''.join('import Owner1007.'+m+'\n' for m in imports)
    root+='namespace Owner1007.PreCage12\nopen NetHack.Sokoban\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
    root+='theorem reverse_checked : Geometry.reverseCheck soko1_2.board=true := by decide +kernel\n'
    for name,family in [('north',N),('ring',R)]:
        n=len(family)
        for label,expr in [('checked',f'FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes {name}Locks {name}Region {name}Paid'),('tagged',f'tagPart {name}Locks {name}Region {name}Paid {name}Allowed')]:
            root+=f'theorem {name}_{label} (i : Fin {n}) : {expr} i=true := by\n obtain ⟨i,h⟩ := i\n have choices : '+' ∨ '.join(f'i={i}' for i in range(n))+' := by omega\n rcases choices with '+'|'.join('rfl' for _ in range(n))+'\n'
            root+=''.join(f' · exact {name}{i}'+('_tags' if label=='tagged' else '')+'\n' for i in range(n))
        root+=f'''theorem {name}_floor (i : Fin {n}) : {name}Region i⊆soko1_2.board.floor := by
 have all : (List.finRange {n}).all (fun i => ({name}Region i).all (fun c => decide (c∈soko1_2.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem {name}_closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes {name}Locks {name}Region {name}Paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse_checked {name}_floor {name}_checked
theorem {name}_unique : ∀ i, ({name}Locks i).Nodup := by decide +kernel
theorem {name}_size : ∀ i, ({name}Locks i).length={len(family[0][0])} := by decide +kernel
#print axioms {name}_closed
'''
    root+='end Owner1007.PreCage12\n'
    (p/'PreCage12.lean').write_text(root)
    (HERE/'precage12_phases.json').write_text(json.dumps(dict(scope='Ten north plus four ring analytic phases; walking BFS only; no boulder-state search',families=rows),indent=2)+'\n')
    print('Generated14specifiedaccessphases;kernelchecksrequired')
if __name__=='__main__':main()
