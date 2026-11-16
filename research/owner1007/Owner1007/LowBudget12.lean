import Owner1007.RightEnergy12
import Owner1007.TightBudget12

namespace Owner1007.LowBudget12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting

theorem initial_partition : soko1_2.initial.boulders.Perm
    (TightBudget12.left ++ RightEnergy12.Right) := by decide +kernel

theorem left_energy_le_five {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cheap : pushes ≤ 220) :
    energy Generated.soko1_2Potential TightBudget12.left outcomes ≤ 5 := by
  have total := logged.all_energy Generated.soko1_2Potential
  have empty : final.holes = [] := completed
  rw [Generated.soko1_2_initial_potential, empty] at total
  simp only [weightSum, Int.add_zero] at total
  have same := energy_perm Generated.soko1_2Potential initial_partition outcomes
  have split := logged.energy_split (show soko1_2.initial.boulders.Nodup by decide +kernel)
    Generated.soko1_2Potential TightBudget12.left RightEnergy12.Right
    (show (TightBudget12.left ++ RightEnergy12.Right).Nodup by decide +kernel)
    (show TightBudget12.left ++ RightEnergy12.Right ⊆ soko1_2.initial.boulders by decide +kernel)
  have right := RightEnergy12.right_energy_three logged completed
  change 3 ≤ energy Generated.soko1_2Potential RightEnergy12.Right outcomes at right
  simp only [Int.ofNat_eq_natCast] at total
  omega

/-- Under the putative220-push budget all eleven ordinary left tokens consume. -/
theorem ordinary_consumed {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cheap : pushes ≤ 220) :
    ∀ cell ∈ TightBudget12.ordinary, endGroup [cell] outcomes = [] :=
  TightBudget12.ordinary_consumed_of_left_energy_le_five logged
    (left_energy_le_five logged completed cheap)

#print axioms left_energy_le_five
#print axioms ordinary_consumed
end Owner1007.LowBudget12
