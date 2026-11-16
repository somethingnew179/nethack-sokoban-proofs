#!/usr/bin/env python3
"""Emit symbolic identities for an EXISTING circuit; no puzzle states/search."""
from pathlib import Path

def source():
    rows=[(75,53,13),(161,105,13),(195,178,7),(201,198,13),
          (219,209,13),(74,52,13),(236,226,13),(258,178,13),
          (309,178,20),(319,314,13),(356,334,13),(374,365,13),
          (430,178,23),(485,450,13),(524,500,13),(586,178,27),
          (658,178,34),(733,178,44)]
    cells=[108,132,133,134,158,159,160,186,187]
    defs=lambda n:', '.join('d'+str(k) for k in range(n+1))
    cases=lambda cs:' <;> '.join('cases h'+str(c)+' : p '+str(c) for c in cs)
    hyps=lambda cs:', '.join('h'+str(c) for c in cs)
    claim=' ∧\n    '.join(f'(d{a} p = d{b} p + d{c} p)' for a,b,c in rows)
    proj=lambda i:'(owner1007_all_factor p)'+'.2'*i+('.1' if i<len(rows)-1 else '')
    return '''/- Symbolic factorization of the existing 217 certificate. No new bound. -/
import NetHack.Sokoban12CostPartition.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
private theorem const_add_ite (c : Bool) (k a b : Int) :
    k + (if c then a else b) = (if c then k+a else k+b) := by cases c <;> rfl
theorem owner1007_all_factor (p : Pattern) :
    '''+claim+' := by\n  '+cases(cells)+' <;>\n    simp ['+defs(733)+', '+hyps(cells)+''', const_add_ite]
theorem owner1007_factors3 (p : Pattern) :
    (d258 p = d178 p + d13 p) ∧
    (d74 p = d52 p + d13 p) ∧
    (d485 p = d450 p + d13 p) :=
  ⟨'''+proj(7)+', '+proj(5)+', '+proj(13)+'''⟩
def owner1007_macroA (p : Pattern) : Pattern :=
  change (change (change p 186 (some 160)) 160 (some 134)) 134 (some 133)
def owner1007_macroB (p : Pattern) : Pattern :=
  change (change p 187 (some 161)) 186 (some 185)
theorem owner1007_left_upper (p : Pattern) : d178 p ≤ 2 := by
  '''+cases(cells)+' <;>\n    simp ['+defs(178)+', '+hyps(cells)+''']
theorem owner1007_leftA (p : Pattern)
    (h160 : p 160 = false) (h134 : p 134 = false) (h133 : p 133 = false) :
    d178 p ≤ d52 (owner1007_macroA p) := by
  '''+cases([108,132,158,159,186,187])+' <;>\n    simp ['+defs(178)+', owner1007_macroA, change, '+hyps(cells)+''']
theorem owner1007_rightA (p : Pattern) :
    d13 (owner1007_macroA p) = d13 p := by
  simp [owner1007_macroA, change, '''+defs(13)+''']
theorem owner1007_rightB (p : Pattern) :
    d13 (owner1007_macroB p) = d13 p := by
  simp [owner1007_macroB, change, '''+defs(13)+''']
theorem owner1007_macroA_bonus (p : Pattern)
    (h160 : p 160 = false) (h134 : p 134 = false) (h133 : p 133 = false) :
    bonus 212 p ≤ bonus 134 (owner1007_macroA p) := by
  change d258 p ≤ d74 (owner1007_macroA p)
  rw [(owner1007_factors3 p).1, (owner1007_factors3 (owner1007_macroA p)).2.1,
    owner1007_rightA]
  have left := owner1007_leftA p h160 h134 h133
  omega
theorem owner1007_macroB_bonus (p : Pattern) :
    bonus 213 p ≤ 2 + bonus 186 (owner1007_macroB p) := by
  change d258 p ≤ 2 + d485 (owner1007_macroB p)
  rw [(owner1007_factors3 p).1, (owner1007_factors3 (owner1007_macroB p)).2.2,
    owner1007_rightB]
  have before := owner1007_left_upper p
  have after := nonnegative450 (owner1007_macroB p)
  omega
theorem owner1007_macro_arithmetic :
    (1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 186 = 0) ∧
    (1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 160 = 0) ∧
    (1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 134 = 2) ∧
    (1 + Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.boulder 187 = 2) ∧
    (1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 186 = 2) := by decide +kernel
#print axioms owner1007_all_factor
#print axioms owner1007_macroA_bonus
#print axioms owner1007_macroB_bonus
#print axioms owner1007_macro_arithmetic
end NetHack.Sokoban12CostPartition
'''

if __name__ == '__main__':
    target=Path(__file__).resolve().parent/'Owner1007/CostPartition12Factor.lean'
    target.write_text(source())
    print('Symbolic Lean proposal emitted; kernel check still required')
