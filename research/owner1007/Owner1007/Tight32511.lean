import Owner1007.UpperUniversalSix11
namespace Owner1007.Tight32511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
/-- Any completion at325 saturates all three disjoint ledgers exactly. -/
theorem budgets {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 pushes=325 ∧ energy soko1_1.initial final U6 outcomes=6 ∧
 energy soko1_1.initial final TightSplit11.B outcomes=4 ∧
 energy soko1_1.initial final Rest outcomes=0 := by
 have upper := UpperUniversalSix11.upper_six logged completed
 have lower := UpperSixBudget11.six_suffices logged completed upper
 have splitOne := Hero315Frame11.energy_split logged U6 TightSplit11.B (by decide +kernel) (by decide +kernel)
 have splitTwo := Hero315Frame11.energy_split logged (U6++TightSplit11.B) Rest (by decide +kernel) (by decide +kernel)
 have perm : soko1_1.initial.boulders.Perm ((U6++TightSplit11.B)++Rest) := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
 have total := total_energy logged completed
 have left := LeftEnergy11.pair_energy_universal logged completed
 change 4≤energy soko1_1.initial final TightSplit11.B outcomes at left
 have rest := energy_nonnegative logged Rest (by decide +kernel) (by decide +kernel)
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms budgets
end Owner1007.Tight32511
