import Owner1007.RightCapacity12Matrices
namespace Owner1007.RightCapacity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem upper_consumed_two {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (gone : endGroup [141,168] outcomes = []) : 2 ≤ energy p [141,168] outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ upperMatrix
  have bound := consumed_energy closed (by decide +kernel) (by decide +kernel) logged
    [141,168] (by decide +kernel) (by decide +kernel) (i:=0)
    (by decide +kernel) (by decide +kernel) gone
  exact bound
theorem low_consumed_three {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (gone : endGroup [246] outcomes = []) : 3 ≤ energy p [246] outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ lowMatrix
  have bound := consumed_energy closed (by decide +kernel) (by decide +kernel) logged
    [246] (by decide +kernel) (by decide +kernel) (i:=0)
    (by decide +kernel) (by decide +kernel) gone
  exact bound
theorem token_consumed_one {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (gone : endGroup [271] outcomes = []) : 1 ≤ energy p [271] outcomes := by
  have closed := PricedCorral.closed_of_check _ _ _ _ _ _ tokenMatrix
  have bound := consumed_energy closed (by decide +kernel) (by decide +kernel) logged
    [271] (by decide +kernel) (by decide +kernel) (i:=0)
    (by decide +kernel) (by decide +kernel) gone
  exact bound

def Q : List Cell := [141,168,246,271]
theorem q_energy_three_of_one {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (small : (endGroup Q outcomes).length ≤ 1) : 3 ≤ energy p Q outcomes := by
  have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
  have splitA := logged.energy_split unique p [141,168] [246,271] (by decide +kernel) (by decide +kernel)
  have splitB := logged.energy_split unique p [246] [271] (by decide +kernel) (by decide +kernel)
  change energy p Q outcomes = energy p [141,168] outcomes + energy p [246,271] outcomes at splitA
  change energy p [246,271] outcomes = energy p [246] outcomes + energy p [271] outcomes at splitB
  have nnUpper := logged.energy_nonnegative Generated.soko1_2_potential_valid [141,168]
  have nnLow := logged.energy_nonnegative Generated.soko1_2_potential_valid [246]
  have nnToken := logged.energy_nonnegative Generated.soko1_2_potential_valid [271]
  change 0 ≤ energy p [141,168] outcomes at nnUpper
  change 0 ≤ energy p [246] outcomes at nnLow
  change 0 ≤ energy p [271] outcomes at nnToken
  by_cases lowGone : endGroup [246] outcomes = []
  · have bound := low_consumed_three logged lowGone
    omega
  · have splitEndsA := TokenAccounting.Logged.end_split logged unique [141,168] [246,271] (by decide +kernel) (by decide +kernel)
    have splitEndsB := TokenAccounting.Logged.end_split logged unique [246] [271] (by decide +kernel) (by decide +kernel)
    have lengthsA := splitEndsA.length_eq
    have lengthsB := splitEndsB.length_eq
    simp only [List.length_append] at lengthsA lengthsB
    change (endGroup [141,168] outcomes).length + (endGroup [246,271] outcomes).length =
      (endGroup Q outcomes).length at lengthsA
    change (endGroup [246] outcomes).length + (endGroup [271] outcomes).length =
      (endGroup [246,271] outcomes).length at lengthsB
    have positive : 1 ≤ (endGroup [246] outcomes).length := by
      cases shape : endGroup [246] outcomes with
      | nil => exact False.elim (lowGone shape)
      | cons c rest => simp only [shape,List.length_cons]; omega
    have upperGone : endGroup [141,168] outcomes = [] := List.eq_nil_of_length_eq_zero (by omega)
    have tokenGone : endGroup [271] outcomes = [] := List.eq_nil_of_length_eq_zero (by omega)
    have upperCost := upper_consumed_two logged upperGone
    have tokenCost := token_consumed_one logged tokenGone
    omega

theorem right_energy_five_of_one {dirs final pushes moves outcomes}
    (potential : Potential)
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (reserved : 2 ≤ energy potential [192,193,218] outcomes)
    (capacity : (endGroup [141,168,246,271] outcomes).length ≤ 1 →
      3 ≤ energy potential [141,168,246,271] outcomes)
    (small : (endGroup [141,168,192,193,218,246,271] outcomes).length ≤ 1) :
    5 ≤ energy potential [141,168,192,193,218,246,271] outcomes := by
  have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
  have perm : ([192,193,218] ++ [141,168,246,271]).Perm [141,168,192,193,218,246,271] := by decide +kernel
  have ends := TokenAccounting.Logged.end_split logged unique [192,193,218] [141,168,246,271]
    (by decide +kernel) (by decide +kernel)
  have count := ends.length_eq
  have sameCount := (endGroup_perm perm outcomes).length_eq
  simp only [List.length_append] at count
  have qSmall : (endGroup [141,168,246,271] outcomes).length ≤ 1 := by omega
  have qBound := capacity qSmall
  have split := logged.energy_split unique potential [192,193,218] [141,168,246,271]
    (by decide +kernel) (by decide +kernel)
  have same := energy_perm potential perm outcomes
  omega

theorem right_small_of318survives {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (survives : endGroup [318] outcomes ≠ []) :
    (endGroup [141,168,192,193,218,246,271] outcomes).length ≤ 1 := by
  have unique : soko1_2.initial.boulders.Nodup := by decide +kernel
  have split := TokenAccounting.Logged.end_split logged unique [318] [141,168,192,193,218,246,271]
    (by decide +kernel) (by decide +kernel)
  have ends := logged.end_subset unique ([318]++[141,168,192,193,218,246,271])
    (by decide +kernel) (by decide +kernel)
  have size := List.Nodup.length_le_of_subset ends.1 ends.2
  have count := split.length_eq
  simp only [List.length_append] at count
  have positive : 1 ≤ (endGroup [318] outcomes).length := by
    cases shape : endGroup [318] outcomes with
    | nil => exact False.elim (survives shape)
    | cons c rest => simp only [List.length_cons]; omega
  have conserved := logged.trace.conservation
  have empty : final.holes=[] := completed
  change 20 + final.holes.length = final.boulders.length + 18 at conserved
  rw [empty] at conserved
  simp only [List.length_nil] at conserved
  omega

theorem right_energy_five_of318survives {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (survives : endGroup [318] outcomes ≠ []) :
    5 ≤ energy p RightEnergy12.Right outcomes :=
  right_energy_five_of_one p logged (RightPrice4.p_energy_two logged completed)
    (q_energy_three_of_one logged) (right_small_of318survives logged completed survives)
#print axioms q_energy_three_of_one
#print axioms right_energy_five_of318survives
end Owner1007.RightCapacity12
