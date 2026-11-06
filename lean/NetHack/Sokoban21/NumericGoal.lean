/- Goal correction is paid by the residual debt of all three survivors. -/
import NetHack.Sokoban21.GoalBounds
namespace NetHack.Sokoban21
open Diagram NetHack.Sokoban.LowerBounds

private theorem live_pattern_eq (pattern : Twelve) :
    support.filter (fun cell => known pattern cell && !deadCells.contains cell) = Projection.occupied pattern := by
  unfold Projection.occupied
  apply List.filter_congr
  intro cell member
  have live := Projection.support_live cell member
  have clear : deadCells.contains cell = false := by
    cases selected : deadCells.contains cell with
    | false => rfl
    | true => exact False.elim (live (List.contains_iff_mem.mp selected))
  simp only [clear, Bool.not_false, Bool.and_true]

theorem goal_bound (dead player : Nat) (pattern : Twelve) (limited : dead ≤ 3)
    (_budget : budgetGuard dead pattern = true)
    (_total : (Projection.occupied pattern).length ≤ 3)
    (live : dead + (support.filter (fun cell => known pattern cell && !deadCells.contains cell)).length ≤ 3) :
    bonus dead player pattern ≤ weightSum debt (Projection.occupied pattern) := by
  have count : dead + (Projection.occupied pattern).length ≤ 3 := by
    simpa only [live_pattern_eq] using live
  have cap_le : d3292 pattern ≤ weightSum debt (Projection.occupied pattern) := by
    rw [cap_semantic, ← occupied_debt]
    exact Int.min_le_right _ _
  have cases : dead = 0 ∨ dead = 1 ∨ dead = 2 ∨ dead = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · have ready : decide (0 + (Projection.occupied pattern).length ≤ 3) = true := by
      simpa only [decide_eq_true_eq] using count
    have guard : d3274 pattern = 1 := by rw [goal0_semantic, ready]; rfl
    exact Int.le_trans (root_goal0 pattern guard player) cap_le
  · have ready : decide (1 + (Projection.occupied pattern).length ≤ 3) = true := by
      simpa only [decide_eq_true_eq] using count
    have guard : d3277 pattern = 1 := by rw [goal1_semantic, ready]; rfl
    exact Int.le_trans (root_goal1 pattern guard player) cap_le
  · have ready : decide (2 + (Projection.occupied pattern).length ≤ 3) = true := by
      simpa only [decide_eq_true_eq] using count
    have guard : d3279 pattern = 1 := by rw [goal2_semantic, ready]; rfl
    exact Int.le_trans (root_goal2 pattern guard player) cap_le
  · have ready : decide (3 + (Projection.occupied pattern).length ≤ 3) = true := by
      simpa only [decide_eq_true_eq] using count
    have guard : d3280 pattern = 1 := by rw [goal3_semantic, ready]; rfl
    exact Int.le_trans (root_goal3 pattern guard player) cap_le

end NetHack.Sokoban21
