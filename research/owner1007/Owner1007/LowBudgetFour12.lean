import Owner1007.LowBudget12
import Owner1007.RightPrice4
namespace Owner1007.LowBudgetFour12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting
open Owner1007.LowBudget12

theorem left_energy_le_four {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cheap : pushes ≤ 220) :
    energy Generated.soko1_2Potential TightBudget12.left outcomes ≤ 4 := by
  have total := logged.all_energy Generated.soko1_2Potential
  have empty : final.holes = [] := completed
  rw [Generated.soko1_2_initial_potential, empty] at total
  simp only [weightSum, Int.add_zero] at total
  have same := energy_perm Generated.soko1_2Potential initial_partition outcomes
  have split := logged.energy_split (show soko1_2.initial.boulders.Nodup by decide +kernel)
    Generated.soko1_2Potential TightBudget12.left RightEnergy12.Right
    (show (TightBudget12.left ++ RightEnergy12.Right).Nodup by decide +kernel)
    (show TightBudget12.left ++ RightEnergy12.Right ⊆ soko1_2.initial.boulders by decide +kernel)
  have right := RightPrice4.right_energy_four logged completed
  change 4 ≤ energy Generated.soko1_2Potential RightEnergy12.Right outcomes at right
  simp only [Int.ofNat_eq_natCast] at total
  omega

#print axioms left_energy_le_four
end Owner1007.LowBudgetFour12
