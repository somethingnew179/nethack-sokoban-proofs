#!/usr/bin/env python3
"""Reuse the existing hero selectors to expose a symbolic bonus sum."""
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
ROWS=[(75,53,13),(161,105,13),(195,178,7),(201,198,13),
      (219,209,13),(74,52,13),(236,226,13),(258,178,13),
      (309,178,20),(319,314,13),(356,334,13),(374,365,13),
      (430,178,23),(485,450,13),(524,500,13),(586,178,27),
      (658,178,34),(733,178,44)]

def source():
    txt=(HERE.parents[1]/'lean/NetHack/Sokoban12CostPartition/Roots.lean').read_text()
    body=re.search(r'def bonus \(player : Cell\) \(p : Pattern\) : Int :=\n(.*?)\ntheorem at29',txt,re.S).group(1)
    groups=re.findall(r'if \((\[[^\]]*\]) : List Cell\)\.contains player then d(\d+) p',body)
    assert len(groups)==18
    out='''import Owner1007.CostPartition12Factor
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
'''
    for name,mapping in [('owner1007_leftBonus',{a:b for a,b,c in ROWS}),
                         ('owner1007_rightBonus',{a:c for a,b,c in ROWS})]:
        b=re.sub(r'd(\d+) p',lambda m:'d'+str(mapping[int(m.group(1))])+' p',body)
        out+='def '+name+' (player : Cell) (p : Pattern) : Int :=\n'+b+'\n'
    proj=lambda i:'(owner1007_all_factor p)'+'.2'*i+('.1' if i<17 else '')
    def proof(i):
        indent='  '+'  '*i
        if i==18:
            return indent+'simp only [bonus, owner1007_leftBonus, owner1007_rightBonus, '+', '.join('if_neg h'+str(j) for j in range(i))+', Int.add_zero]\n'
        group,_=groups[i]
        facts=', '.join(['if_neg h'+str(j) for j in range(i)]+['if_pos h'+str(i)])
        inner=proof(i+1).splitlines()
        inner[0]=indent+'· '+inner[0].lstrip()
        return (indent+'by_cases h'+str(i)+' : ('+group+' : List Cell).contains player = true\n'
                +indent+'· simpa only [bonus, owner1007_leftBonus, owner1007_rightBonus, '+facts+'] using '+proj(i)+'\n'
                +'\n'.join(inner)+'\n')
    out+='theorem owner1007_bonus_factor (player : Cell) (p : Pattern) :\n    bonus player p = owner1007_leftBonus player p + owner1007_rightBonus player p := by\n'+proof(0)
    out+='''theorem owner1007_right13_formula (p : Pattern) :
    d13 p = (if p 192 && p 193 then (2 : Int) else 0) +
      (if p 141 && p 168 && p 271 then (1 : Int) else 0) := by
  cases h141 : p 141 <;> cases h168 : p 168 <;>
    cases h192 : p 192 <;> cases h193 : p 193 <;>
    cases h271 : p 271 <;>
    simp [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,
      h141,h168,h192,h193,h271]
#print axioms owner1007_bonus_factor
#print axioms owner1007_right13_formula
end NetHack.Sokoban12CostPartition
'''
    return out

if __name__=='__main__':
    (HERE/'Owner1007/CostPartition12Split.lean').write_text(source())
    print('Global split proposal emitted; kernel check still required')
