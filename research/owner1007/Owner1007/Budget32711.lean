import Owner1007.ConsumedParity11
import Owner1007.Lower327
import Owner1007.TightSurvivors11
namespace Owner1007.Budget32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem upper_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cap : energy soko1_1.initial final U6 outcomes≤8) :
 endGroup U6 outcomes=[] := by
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide) (by decide)
 change energy soko1_1.initial final U6 outcomes=_ at split
 have pair := PairBound11.pair_energy logged completed
 change 2≤energy soko1_1.initial final TightSplit11.A outcomes at pair
 have bound141 := energy_subset (Trace.nil soko1_1.initial) logged [141] C
   (by decide) (by decide) (by decide) (by decide) (by decide)
 have debts : U6.all (fun c=>decide (c=141∨value soko1_1.initial [c]< -8))=true := by decide +kernel
 apply TightSurvivors11.all_nil logged (by decide) U6 (by decide) (by decide)
 intro cell member
 rcases of_decide_eq_true (List.all_eq_true.mp debts cell member) with rfl|debt
 ·exact TightSurvivors11.singleton_nil logged completed [141] (by decide) (by decide) (by decide) 6 (by omega)
    141 (by decide) (by decide +kernel)
 ·exact TightSurvivors11.singleton_nil logged completed U6 (by decide) (by decide) (by decide) 8 cap cell member debt

theorem left_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cap : energy soko1_1.initial final TightSplit11.B outcomes≤6) :
 endGroup TightSplit11.B outcomes=[] := by
 have debts : TightSplit11.B.all (fun c=>decide (value soko1_1.initial [c]< -6))=true := by decide +kernel
 apply TightSurvivors11.all_nil logged (by decide) TightSplit11.B (by decide) (by decide)
 intro cell member
 exact TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide) 6 cap cell member
   (of_decide_eq_true (List.all_eq_true.mp debts cell member))

theorem rest_negative_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cap : energy soko1_1.initial final Rest outcomes≤2) :
 endGroup TightSurvivors11.negativeRest outcomes=[] := by
 have debts : TightSurvivors11.negativeRest.all (fun c=>decide (value soko1_1.initial [c]< -2))=true := by decide +kernel
 apply TightSurvivors11.all_nil logged (by decide) TightSurvivors11.negativeRest (by decide) (by decide)
 intro cell member
 have memberRest := (show TightSurvivors11.negativeRest⊆Rest from by decide) member
 exact TightSurvivors11.singleton_nil logged completed Rest (by decide) (by decide) (by decide) 2 cap cell memberRest
   (of_decide_eq_true (List.all_eq_true.mp debts cell member))

theorem modes {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) :
 pushes=327 ∧
 ((energy soko1_1.initial final U6 outcomes=8 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧energy soko1_1.initial final Rest outcomes=0) ∨
  (energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=6 ∧energy soko1_1.initial final Rest outcomes=0) ∨
  (energy soko1_1.initial final U6 outcomes=6 ∧energy soko1_1.initial final TightSplit11.B outcomes=4 ∧energy soko1_1.initial final Rest outcomes=2)) := by
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
 have upperCap : energy soko1_1.initial final U6 outcomes≤8 := by omega
 have leftCap : energy soko1_1.initial final TightSplit11.B outcomes≤6 := by omega
 have evenUpper := ConsumedParity11.consumed_even logged completed U6 (by decide) (by decide) (upper_gone logged completed upperCap)
 have evenLeft := ConsumedParity11.consumed_even logged completed TightSplit11.B (by decide) (by decide) (left_gone logged completed leftCap)
 have lower := Lower327.pushes_lower_bound logged.trace completed
 omega
#print axioms upper_gone
#print axioms left_gone
#print axioms rest_negative_gone
#print axioms modes
end Owner1007.Budget32711
