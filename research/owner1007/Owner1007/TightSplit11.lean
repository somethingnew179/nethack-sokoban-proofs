import Owner1007.HeroEnergyPartitions11
import Owner1007.PairBound11
import Owner1007.LeftEnergy11
namespace Owner1007.TightSplit11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def A : List Cell := [139,191]
def B : List Cell := [186,212]
def Rest : List Cell := [133,135,137,141,188,193,264,266,268,293,315,317,321,367]

theorem exact_energy_split {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    Int.ofNat pushes - 315 = energy soko1_1.initial final A outcomes +
      energy soko1_1.initial final B outcomes + energy soko1_1.initial final Rest outcomes := by
  have perm : soko1_1.initial.boulders.Perm ((A ++ B) ++ Rest) := by decide +kernel
  have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
  have splitOne := Hero315Frame11.energy_split logged A B (by decide +kernel) (by decide +kernel)
  have splitTwo := Hero315Frame11.energy_split logged (A ++ B) Rest (by decide +kernel) (by decide +kernel)
  have total := total_energy logged completed
  omega

/-- Compact structural reconstruction of the original321 lower bound. -/
theorem pushes_lower_bound {dirs final pushes moves}
    (trace : Trace soko1_1.board soko1_1.initial dirs final pushes moves)
    (completed : Goal final) : 321 ≤ pushes := by
  obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
  have split := exact_energy_split logged completed
  have a := PairBound11.pair_energy logged completed
  have b := LeftEnergy11.pair_energy_universal logged completed
  have rest := energy_nonnegative logged Rest (by decide +kernel) (by decide +kernel)
  change 2 ≤ energy soko1_1.initial final A outcomes at a
  change 4 ≤ energy soko1_1.initial final B outcomes at b
  simp only [Int.ofNat_eq_natCast] at split
  omega

/-- Tightness records the disjoint budget needed for subsequent coaccessibility arguments. -/
theorem tight {dirs final pushes moves outcomes}
    (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
    (completed : Goal final) (cheap : pushes ≤ 321) :
    energy soko1_1.initial final A outcomes = 2 ∧
    energy soko1_1.initial final B outcomes = 4 ∧
    energy soko1_1.initial final Rest outcomes = 0 := by
  have split := exact_energy_split logged completed
  have a := PairBound11.pair_energy logged completed
  have b := LeftEnergy11.pair_energy_universal logged completed
  have rest := energy_nonnegative logged Rest (by decide +kernel) (by decide +kernel)
  change 2 ≤ energy soko1_1.initial final A outcomes at a
  change 4 ≤ energy soko1_1.initial final B outcomes at b
  simp only [Int.ofNat_eq_natCast] at split
  omega
#print axioms exact_energy_split
#print axioms pushes_lower_bound
#print axioms tight
end Owner1007.TightSplit11
