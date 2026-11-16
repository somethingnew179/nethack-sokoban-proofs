import Owner1007.Budget327TwoModes11
import Owner1007.ModeCLeft11
namespace Owner1007.Budget327OnlyB11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
/-- Any hypothetical original327 completion must spend exactly6/6/0.
This necessary restriction is not an impossibility proof or a327 witness. -/
theorem mode {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) :
 pushes=327 ∧energy soko1_1.initial final U6 outcomes=6 ∧
 energy soko1_1.initial final TightSplit11.B outcomes=6 ∧energy soko1_1.initial final Rest outcomes=0 := by
 obtain ⟨count,modes⟩ := Budget327TwoModes11.modes logged completed cheap
 rcases modes with middle|last
 ·exact ⟨count,middle⟩
 ·exact False.elim (ModeCLeft11.impossible logged completed cheap (by omega) (by omega) (by omega))
#print axioms mode
end Owner1007.Budget327OnlyB11
