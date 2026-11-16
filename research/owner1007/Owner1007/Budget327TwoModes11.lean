import Owner1007.Zero186Strong32711
import Owner1007.ModeLeftSix32711
namespace Owner1007.Budget327TwoModes11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
theorem left_four_rest_zero_impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (upper : energy soko1_1.initial final U6 outcomes≤8)
 (left : energy soko1_1.initial final TightSplit11.B outcomes=4)
 (rest : energy soko1_1.initial final Rest outcomes=0) : False := by
 have zero := ModeLeftSix32711.modeA_zero186 logged completed cheap left rest
 exact Zero186Strong32711.impossible logged completed cheap upper (by omega) zero

/-- The Upper8/Left4/Rest0 alternative is now excluded by actual chronology.
The remaining two alternatives do not themselves prove328. -/
theorem modes {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) :
 pushes=327 ∧
 ((energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=6 ∧
   energy soko1_1.initial final Rest outcomes=0) ∨
  (energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧
   energy soko1_1.initial final Rest outcomes=2)) := by
 obtain ⟨count,alternatives⟩ := Budget32711.modes logged completed cheap
 refine ⟨count,?_⟩
 rcases alternatives with ⟨upper,left,rest⟩|middle|last
 · exact False.elim (left_four_rest_zero_impossible logged completed cheap (by omega) left rest)
 · exact Or.inl middle
 · exact Or.inr last
#print axioms left_four_rest_zero_impossible
#print axioms modes
end Owner1007.Budget327TwoModes11
