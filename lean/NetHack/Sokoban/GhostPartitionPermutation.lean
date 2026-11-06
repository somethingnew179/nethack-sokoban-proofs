/- Canonical ordering of a persistent group does not change its update or
its ownership charge. No spatial erasure or hero-region quotient is used. -/
import NetHack.Sokoban.GhostPartition
namespace NetHack.Sokoban.GhostPartition
open HazardPattern

theorem update_permutation (a b : List Cell) (related : a.Perm b) (outcome : Outcome) :
    (update a outcome).Perm (update b outcome) := by
  cases outcome with
  | walk _ => exact related
  | push source result =>
    by_cases owner : source ∈ a
    · have other : source ∈ b := related.mem_iff.mp owner
      simp only [update,move,if_pos owner,if_pos other]
      have erased := List.Perm.erase source related
      cases result with
      | stay landing => exact erased.cons landing
      | fill hole => exact erased
    · have other : source ∉ b := fun h => owner (related.mem_iff.mpr h)
      simpa only [update,move,if_neg owner,if_neg other] using related

theorem charge_permutation (holeWeight : Cell → Int) (a b : List Cell) (related : a.Perm b)
    (outcome : Outcome) : charge holeWeight a outcome = charge holeWeight b outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result =>
    have same : source ∈ a ↔ source ∈ b := related.mem_iff
    cases result <;> simp only [charge,same]

end NetHack.Sokoban.GhostPartition
