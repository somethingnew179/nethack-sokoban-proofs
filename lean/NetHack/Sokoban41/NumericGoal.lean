/- Stage-only goal-bound closure from a checked finite occupancy diagram. -/
import NetHack.Sokoban41.GoalBounds
namespace NetHack.Sokoban41
open Diagram NetHack.Sokoban.LowerBounds

theorem goal_bound (dead player : Nat) (pattern : Ten) (limited : dead ≤ 1)
    (budget : budgetGuard dead pattern = true)
    (total : (Projection.occupied pattern).length ≤ 1)
    (live : dead + (support.filter (fun cell => known pattern cell && !deadCells.contains cell)).length ≤ 1) :
    bonus dead player pattern ≤ weightSum debt (Projection.occupied pattern) := by
  have cap_le : d816 pattern ≤ weightSum debt (Projection.occupied pattern) := by
    rw [cap_semantic]
    exact Int.min_le_right _ _
  have cases : dead = 0 ∨ dead = 1 := by omega
  rcases cases with rfl | rfl
  · have totalBool : decide ((Projection.occupied pattern).length ≤ 1) = true := by
      simpa only [decide_eq_true_eq] using total
    have ready : (budgetGuard 0 pattern && decide ((Projection.occupied pattern).length ≤ 1)) = true :=
      Bool.and_eq_true_iff.mpr ⟨budget, totalBool⟩
    have guard : d793 pattern = 1 := by
      rw [goal0_semantic, ready]
      rfl
    exact Int.le_trans (root_goal0 pattern guard player) cap_le
  · have empty : (support.filter (fun cell => known pattern cell && !deadCells.contains cell)).length = 0 := by omega
    have guard : d800 pattern = 1 := by
      rw [goal1_semantic]
      simp only [empty, decide_true, ↓reduceIte]
    exact Int.le_trans (root_goal1 pattern guard player) cap_le

end NetHack.Sokoban41
