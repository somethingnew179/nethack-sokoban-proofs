import Owner1007.NorthBound12
import Owner1007.NorthWrap12
import Owner1007.RightCapacity12
import Owner1007.Final222
import Owner1007.CheapNorth12

namespace Owner1007.Lower222
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential

theorem north_bound {dirs final pushes moves}
    (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves)
    (completed : Goal final) : 222 ≤ 1 + pushes := by
  obtain ⟨outcomes, logged⟩ := log_exists trace (by decide +kernel)
  have whole := NorthWrap12.canonical_north logged
  have right := RightPrice4.right_energy_four whole completed
  have capacity := fun survives => RightCapacity12.right_energy_five_of318survives whole completed survives
  have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
  have same : energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) =
      energy p NorthBound12.G outcomes :=
    (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
  have branch : 4 ≤ energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) ∨
      (3 ≤ energy p Final222.G (.walk 397 :: .push 371 (.stay 345) :: outcomes) ∧
        endGroup [318] (.walk 397 :: .push 371 (.stay 345) :: outcomes) ≠ []) := by
    rcases NorthBound12.g_cases logged completed with four | ⟨three,survives⟩
    · exact Or.inl (by rw [same]; exact four)
    · refine Or.inr ⟨by rw [same]; exact three, ?_⟩
      change endGroup (update [318] (.push 371 (.stay 345))) outcomes ≠ []
      have kept : update [318] (.push 371 (.stay 345)) = [318] := by decide +kernel
      rw [kept]
      exact survives
  exact Final222.conditional_222 whole completed right capacity branch

/-- Universal lower bound for every original canonical full-map completing Trace. -/
theorem pushes_lower_bound {dirs final pushes moves}
    (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
    (completed : Goal final) : 222 ≤ pushes := by
  by_cases large : 225 ≤ pushes
  · omega
  · obtain ⟨q,m,ds,count,north⟩ := CheapNorth12.all_cheap_completions_start_north
      trace completed (by omega)
    have bound := north_bound north completed
    omega

#print axioms north_bound
#print axioms pushes_lower_bound
end Owner1007.Lower222
