#!/usr/bin/env python3
"""Emit direction-wise kernel checks for explicitly supplied symbolic cuts."""
from diagnose import HERE, DIRS


def phase_file(name, tag, locks, region, paid, index, lemma):
    code = f'import Owner1007.{name}Data\nnamespace Owner1007.{name}\nopen NetHack.Sokoban\n'
    code += 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for direction in DIRS:
        code += (f'theorem {tag}_{direction} : FastCorral11.walkPart soko1_1.board {locks} {region} '
                 f'⟨{index},by decide⟩ .{direction} = true := by decide +kernel\n')
    code += (f'theorem {tag}_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes '
             f'{locks} {region} {paid} ⟨{index},by decide⟩ = true := by decide +kernel\n')
    code += (f'theorem {lemma} : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes '
             f'{locks} {region} {paid} ⟨{index},by decide⟩ = true := by\n'
             '  apply FastCorral11.node_of_parts\n  · intro dir\n    cases dir with\n')
    for direction in DIRS:
        code += f'    | {direction} => exact {tag}_{direction}\n'
    code += f'  · exact {tag}_pushes\n#print axioms {lemma}\nend Owner1007.{name}\n'
    module = name + 'Check' + tag.title()
    (HERE/f'Owner1007/{module}.lean').write_text(code)
    return module


def checked_family(n, lemma='checked'):
    code = (f'theorem {lemma} (i : Fin {n}) : FastCorral11.nodeCheck soko1_1.board '
            'soko1_1.initial.holes locks region paid i = true := by\n'
            '  obtain ⟨i,bound⟩ := i\n  have choices : ')
    code += ' ∨ '.join(f'i={i}' for i in range(n)) + ' := by omega\n  rcases choices with '
    code += '|'.join('rfl' for _ in range(n)) + '\n'
    code += ''.join(f'  · exact node{i}\n' for i in range(n))
    return code


def family_finish(n, size=None):
    size = size if size is not None else 2 if n == 2 else 3 if n == 4 else 4
    return f'''theorem region_floor (i : Fin {n}) : region i ⊆ soko1_1.board.floor := by
  have all : (List.finRange {n}).all (fun i => (region i).all (fun c => decide (c ∈ soko1_1.board.floor))) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked region_floor checked
theorem unique (i : Fin {n}) : (locks i).Nodup := by
  have all : (List.finRange {n}).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin {n}) : (locks i).length = {size} := by
  have all : (List.finRange {n}).all (fun i => decide ((locks i).length = {size})) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
#print axioms closed
'''


def main():
    for name,n in [('LeftPair11',2),('WestAfter11',4),('Parked18811',9)]:
        modules=[]
        if name=='LeftPair11':
            modules.append(phase_file(name,'first','cut0Locks','cut0Region','cut0Paid',0,'first_checked'))
        for i in range(n):
            modules.append(phase_file(name,f'phase{i}','locks','region','paid',i,f'node{i}'))
        code='\n'.join('import Owner1007.'+m for m in modules)
        code+=f'\nnamespace Owner1007.{name}\nopen NetHack.Sokoban\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        if name=='LeftPair11':
            code+='''theorem first_floor (i : Fin 1) : cut0Region i ⊆ soko1_1.board.floor := by
  have all : (cut0Region ⟨0,by decide⟩).all (fun c => decide (c ∈ soko1_1.board.floor)) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem first_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes cut0Locks cut0Region cut0Paid := by
  apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked first_floor
  intro i
  have same : i=⟨0,by decide⟩ := Fin.ext (by omega)
  simpa only [same] using first_checked
#print axioms first_closed
'''
        code+=checked_family(n)+family_finish(n)+f'end Owner1007.{name}\n'
        (HERE/f'Owner1007/{name}.lean').write_text(code)
    name='PostCuts11'
    modules=[phase_file(name,t,t+'Locks',t+'Region',t+'Paid',0,t+'_checked') for t in ('right','entry')]
    code='\n'.join('import Owner1007.'+m for m in modules)+f'\nnamespace Owner1007.{name}\nopen NetHack.Sokoban\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for tag in ('right','entry'):
        code+=f'''theorem {tag}_floor (i : Fin 1) : {tag}Region i ⊆ soko1_1.board.floor := by
  have all : ({tag}Region ⟨0,by decide⟩).all (fun c => decide (c ∈ soko1_1.board.floor)) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem {tag}_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes {tag}Locks {tag}Region {tag}Paid := by
  apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked {tag}_floor
  intro i
  have same : i=⟨0,by decide⟩ := Fin.ext (by omega)
  simpa only [same] using {tag}_checked
#print axioms {tag}_closed
'''
    code+=f'end Owner1007.{name}\n'
    (HERE/f'Owner1007/{name}.lean').write_text(code)
    print('Generated direction-wise checks for eighteen supplied symbolic phases; kernel check required')


if __name__=='__main__':
    main()
