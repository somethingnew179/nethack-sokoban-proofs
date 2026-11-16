import Owner1007.RightEnergy12

namespace Owner1007.Final222
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
def U : List Cell := [108,158,159,186,187]
def G : List Cell := [210,237,238,263,265,318,371]
def R : List Cell := [141,168,192,193,218,246,271]
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem upper_energy_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 2 ≤ energy p U outcomes := by
  have bound := RightEnergy12.raw_group_energy logged (Trace.nil _) U
    (by decide +kernel) (by decide +kernel) completed
  have bonus : RightEnergy12.cert.bonus soko1_2.initial.player (PatternCorrection.project U) = 2 := by decide +kernel
  rw [bonus] at bound
  exact bound

theorem total_energy {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    energy p U outcomes + energy p G outcomes + energy p [213] outcomes + energy p R outcomes =
      Int.ofNat pushes - 212 := by
  have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
  have perm : (U ++ (G ++ ([213] ++ R))).Perm soko1_2.initial.boulders := by decide +kernel
  have a := logged.energy_split unique p U (G++([213]++R)) (by decide +kernel) (by decide +kernel)
  have b := logged.energy_split unique p G ([213]++R) (by decide +kernel) (by decide +kernel)
  have c := logged.energy_split unique p [213] R (by decide +kernel) (by decide +kernel)
  have same := energy_perm p perm outcomes
  have total := logged.all_energy p
  have empty : final.holes=[] := completed
  have initial : p.value soko1_2.initial=212 := by decide +kernel
  rw [initial,empty] at total
  simp only [weightSum] at total
  omega

/-- Arithmetic assembly only; the caller must supply the checked branch disjunction. -/
theorem conditional_222 {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final)
    (rightFour : 4 ≤ energy p R outcomes)
    (rightCapacity : endGroup [318] outcomes ≠ [] → 5 ≤ energy p R outcomes)
    (branch : 4 ≤ energy p G outcomes ∨
      (3 ≤ energy p G outcomes ∧ endGroup [318] outcomes ≠ [])) :
    222 ≤ pushes := by
  have upper := upper_energy_two logged completed
  have total := total_energy logged completed
  simp only [Int.ofNat_eq_natCast] at total
  have other := logged.energy_nonnegative Generated.soko1_2_potential_valid [213]
  change 0 ≤ energy p [213] outcomes at other
  rcases branch with four | ⟨three,survives⟩
  · omega
  · have five := rightCapacity survives
    omega

#print axioms upper_energy_two
#print axioms conditional_222
end Owner1007.Final222
