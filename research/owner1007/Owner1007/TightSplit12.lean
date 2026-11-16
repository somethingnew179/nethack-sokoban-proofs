import Owner1007.BottomEnergy12
import Owner1007.TightBudget12

namespace Owner1007.TightSplit12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.PatternCorrection
open Owner1007.TokenAccounting
abbrev raw := Generated.soko1_2Potential
abbrev Ordinary := TightBudget12.ordinary
abbrev Bottom := BottomEnergy12.Bottom
abbrev Right := RightEnergy12.Right

theorem ordinary_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 2 ≤ energy raw Ordinary outcomes := by
  have bound := RightEnergy12.raw_group_energy logged (Trace.nil _) Ordinary
    (by decide +kernel) (by decide +kernel) completed
  have bonus : RightEnergy12.cert.bonus soko1_2.initial.player (project Ordinary) = 2 := by decide +kernel
  rw [bonus] at bound
  exact bound

theorem exact_energy_split {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    energy raw Ordinary outcomes + energy raw Bottom outcomes + energy raw Right outcomes =
      Int.ofNat pushes - 212 := by
  have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
  have total := logged.all_energy raw
  have empty : final.holes = [] := completed
  rw [Generated.soko1_2_initial_potential, empty] at total
  simp only [weightSum, Int.add_zero] at total
  have splitOne := logged.energy_split unique raw Ordinary Bottom (by decide +kernel) (by decide +kernel)
  have splitTwo := logged.energy_split unique raw (Ordinary ++ Bottom) Right (by decide +kernel) (by decide +kernel)
  have perm : ((Ordinary ++ Bottom) ++ Right).Perm soko1_2.initial.boulders := by decide +kernel
  have same := energy_perm raw perm outcomes
  simp only [Int.ofNat_eq_natCast] at total ⊢
  omega

/-- A compact fresh220 proof: ordinary2 + bottom2 + right4, with exact ownership. -/
theorem pushes_lower_bound {dirs final pushes moves}
    (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
    (completed : Goal final) : 220 ≤ pushes := by
  obtain ⟨outcomes, logged⟩ := log_exists trace (by decide +kernel)
  have split := exact_energy_split logged completed
  have ordinary := ordinary_energy_two logged completed
  have bottom := BottomEnergy12.bottom_energy_two logged
  have right := RightPrice4.right_energy_four logged completed
  change 2 ≤ energy raw Bottom outcomes at bottom
  change 4 ≤ energy raw Right outcomes at right
  simp only [Int.ofNat_eq_natCast] at split
  omega

theorem tight_budget {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cheap : pushes ≤ 220) :
    energy raw Ordinary outcomes = 2 ∧ energy raw Bottom outcomes = 2 ∧
      energy raw Right outcomes = 4 := by
  have split := exact_energy_split logged completed
  have ordinary := ordinary_energy_two logged completed
  have bottom := BottomEnergy12.bottom_energy_two logged
  have right := RightPrice4.right_energy_four logged completed
  change 2 ≤ energy raw Bottom outcomes at bottom
  change 4 ≤ energy raw Right outcomes at right
  simp only [Int.ofNat_eq_natCast] at split
  omega

#print axioms pushes_lower_bound
#print axioms tight_budget
end Owner1007.TightSplit12
