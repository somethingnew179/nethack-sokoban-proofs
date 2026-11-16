import Owner1007.ConsumedParity11
import Owner1007.Lower326
import Owner1007.UpperEightBudget11
import Owner1007.TightSurvivors11
namespace Owner1007.Tight32611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem budgets {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) :
 pushes=326 ∧energy soko1_1.initial final U6 outcomes=6 ∧
 energy soko1_1.initial final TightSplit11.B outcomes=4 ∧
 energy soko1_1.initial final Rest outcomes=1 := by
 have upper := UpperUniversalSix11.upper_six logged completed
 have splitOne := Hero315Frame11.energy_split logged U6 TightSplit11.B (by decide) (by decide)
 have splitTwo := Hero315Frame11.energy_split logged (U6++TightSplit11.B) Rest (by decide) (by decide)
 have perm : soko1_1.initial.boulders.Perm ((U6++TightSplit11.B)++Rest) := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
 have total := total_energy logged completed
 have left := LeftEnergy11.pair_energy_universal logged completed
 change 4≤energy soko1_1.initial final TightSplit11.B outcomes at left
 have rest := energy_nonnegative logged Rest (by decide) (by decide)
 simp only [Int.ofNat_eq_natCast] at total
 have upperCap : energy soko1_1.initial final U6 outcomes≤7 := by omega
 have leftCap : energy soko1_1.initial final TightSplit11.B outcomes≤5 := by omega
 have upperDebts : U6.all (fun c=>decide (c=141∨value soko1_1.initial [c]< -7))=true := by decide +kernel
 have leftDebts : TightSplit11.B.all (fun c=>decide (value soko1_1.initial [c]< -5))=true := by decide +kernel
 have upperGone : endGroup U6 outcomes=[] := by
  apply TightSurvivors11.all_nil logged (by decide) U6 (by decide) (by decide)
  intro c member
  rcases of_decide_eq_true (List.all_eq_true.mp upperDebts c member) with rfl|debt
  ·have budget := UpperEightBudget11.cheap_others_six logged completed (by omega) 141 (by decide)
   exact TightSurvivors11.singleton_nil logged completed [141] (by decide) (by decide) (by decide) 5 (by omega)
     141 (by decide) (by decide +kernel)
  ·exact TightSurvivors11.singleton_nil logged completed U6 (by decide) (by decide) (by decide) 7 upperCap c member debt
 have leftGone : endGroup TightSplit11.B outcomes=[] := by
  apply TightSurvivors11.all_nil logged (by decide) TightSplit11.B (by decide) (by decide)
  intro c member
  exact TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 5 leftCap c member
    (of_decide_eq_true (List.all_eq_true.mp leftDebts c member))
 have evenUpper := ConsumedParity11.consumed_even logged completed U6 (by decide) (by decide) upperGone
 have evenLeft := ConsumedParity11.consumed_even logged completed TightSplit11.B (by decide) (by decide) leftGone
 have lower := Lower326.pushes_lower_bound logged.trace completed
 omega
#print axioms budgets
end Owner1007.Tight32611
