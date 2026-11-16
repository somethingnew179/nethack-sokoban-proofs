import Owner1007.Budget32711
import Owner1007.Lower328
namespace Owner1007.Budget32811
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem left_gone_seven {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cap : energy soko1_1.initial final TightSplit11.B outcomes≤7) :
 endGroup TightSplit11.B outcomes=[] := by
 have debts : TightSplit11.B.all (fun c=>decide (value soko1_1.initial [c]< -7))=true := by decide +kernel
 apply TightSurvivors11.all_nil logged (by decide) TightSplit11.B (by decide) (by decide)
 intro cell member
 exact TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 7 cap cell member
  (of_decide_eq_true (List.all_eq_true.mp debts cell member))

/-- The next budget has three absorbed-Upper modes and a real survivor alternative.
The fourth alternative is retained explicitly; no claim of329 is made. -/
theorem modes {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤328) : pushes=328 ∧
 ((energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧energy soko1_1.initial final Rest outcomes=3) ∨
  (energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=6 ∧energy soko1_1.initial final Rest outcomes=1) ∨
  (energy soko1_1.initial final U6 outcomes=8 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧energy soko1_1.initial final Rest outcomes=1) ∨
  (energy soko1_1.initial final U6 outcomes=9 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧energy soko1_1.initial final Rest outcomes=0 ∧endGroup U6 outcomes≠[])) := by
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
 have upperCap : energy soko1_1.initial final U6 outcomes≤9 := by omega
 have leftCap : energy soko1_1.initial final TightSplit11.B outcomes≤7 := by omega
 have evenLeft := ConsumedParity11.consumed_even logged completed TightSplit11.B (by decide) (by decide) (left_gone_seven logged completed leftCap)
 have lower := Lower328.pushes_lower_bound logged.trace completed
 have exactPush : pushes=328 := by omega
 refine ⟨exactPush,?_⟩
 by_cases cap : energy soko1_1.initial final U6 outcomes≤8
 ·have evenUpper := ConsumedParity11.consumed_even logged completed U6 (by decide) (by decide) (Budget32711.upper_gone logged completed cap)
  omega
 ·have missing : endGroup U6 outcomes≠[] := by
   intro gone
   have evenUpper:=ConsumedParity11.consumed_even logged completed U6 (by decide) (by decide) gone
   omega
  exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,missing⟩))
#print axioms left_gone_seven
#print axioms modes
end Owner1007.Budget32811
