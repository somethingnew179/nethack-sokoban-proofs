import Owner1007.Final222
namespace Owner1007.Final224
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Final222

/-- Conditional assembly; it does not assert the stronger branch for every trace. -/
theorem conditional_224 {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final)
    (rightFour : 4 ≤ energy p R outcomes)
    (rightCapacity : endGroup [318] outcomes ≠ [] → 5 ≤ energy p R outcomes)
    (branch : 6 ≤ energy p G outcomes ∨
      (5 ≤ energy p G outcomes ∧ endGroup [318] outcomes ≠ [])) :
    224 ≤ pushes := by
  have upper := upper_energy_two logged completed
  have total := total_energy logged completed
  simp only [Int.ofNat_eq_natCast] at total
  have other := logged.energy_nonnegative Generated.soko1_2_potential_valid [213]
  change 0 ≤ energy p [213] outcomes at other
  rcases branch with six | ⟨five,survives⟩
  · omega
  · have right := rightCapacity survives
    omega
#print axioms conditional_224
end Owner1007.Final224
