/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers50
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk637_2 (pattern : Twelve) : walkGuard ⟨205,184,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk637_2 : WalkBound ⟨205,184,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk637_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk637_3 (pattern : Twelve) : walkGuard ⟨205,184,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk637_3 : WalkBound ⟨205,184,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk637_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk638_0 (pattern : Twelve) : walkGuard ⟨206,186,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk638_0 : WalkBound ⟨206,186,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk638_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk638_1 (pattern : Twelve) : walkGuard ⟨206,186,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk638_1 : WalkBound ⟨206,186,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk638_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk638_2 (pattern : Twelve) : walkGuard ⟨206,186,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk638_2 : WalkBound ⟨206,186,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk638_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk638_3 (pattern : Twelve) : walkGuard ⟨206,186,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk638_3 : WalkBound ⟨206,186,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk638_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk639_0 (pattern : Twelve) : walkGuard ⟨206,205,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk639_0 : WalkBound ⟨206,205,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk639_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk639_1 (pattern : Twelve) : walkGuard ⟨206,205,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk639_1 : WalkBound ⟨206,205,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk639_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk639_2 (pattern : Twelve) : walkGuard ⟨206,205,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk639_2 : WalkBound ⟨206,205,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk639_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk639_3 (pattern : Twelve) : walkGuard ⟨206,205,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk639_3 : WalkBound ⟨206,205,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk639_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk640_0 (pattern : Twelve) : walkGuard ⟨206,187,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk640_0 : WalkBound ⟨206,187,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk640_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk640_1 (pattern : Twelve) : walkGuard ⟨206,187,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk640_1 : WalkBound ⟨206,187,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk640_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk640_2 (pattern : Twelve) : walkGuard ⟨206,187,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk640_2 : WalkBound ⟨206,187,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk640_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk640_3 (pattern : Twelve) : walkGuard ⟨206,187,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk640_3 : WalkBound ⟨206,187,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk640_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk641_0 (pattern : Twelve) : walkGuard ⟨206,185,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk641_0 : WalkBound ⟨206,185,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk641_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk641_1 (pattern : Twelve) : walkGuard ⟨206,185,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk641_1 : WalkBound ⟨206,185,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk641_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk641_2 (pattern : Twelve) : walkGuard ⟨206,185,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk641_2 : WalkBound ⟨206,185,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk641_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk641_3 (pattern : Twelve) : walkGuard ⟨206,185,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk641_3 : WalkBound ⟨206,185,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk641_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem push0_0 : PushBound ⟨22,21,23,23,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push0_1 (pattern : Twelve) : pushGuard ⟨22,21,23,23,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push0_1 : PushBound ⟨22,21,23,23,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push0_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push0_2 (pattern : Twelve) : pushGuard ⟨22,21,23,23,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push0_2 : PushBound ⟨22,21,23,23,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push0_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push0_3 (pattern : Twelve) : pushGuard ⟨22,21,23,23,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push0_3 : PushBound ⟨22,21,23,23,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push0_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push1_0 : PushBound ⟨22,23,21,21,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push1_1 (pattern : Twelve) : pushGuard ⟨22,23,21,21,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push1_1 : PushBound ⟨22,23,21,21,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push1_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push1_2 (pattern : Twelve) : pushGuard ⟨22,23,21,21,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push1_2 : PushBound ⟨22,23,21,21,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push1_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push1_3 (pattern : Twelve) : pushGuard ⟨22,23,21,21,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push1_3 : PushBound ⟨22,23,21,21,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push1_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push2_0 : PushBound ⟨23,22,24,24,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push2_1 (pattern : Twelve) : pushGuard ⟨23,22,24,24,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push2_1 : PushBound ⟨23,22,24,24,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push2_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push2_2 (pattern : Twelve) : pushGuard ⟨23,22,24,24,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push2_2 : PushBound ⟨23,22,24,24,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push2_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push2_3 (pattern : Twelve) : pushGuard ⟨23,22,24,24,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push2_3 : PushBound ⟨23,22,24,24,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push2_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push3_0 : PushBound ⟨23,24,22,22,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push3_1 (pattern : Twelve) : pushGuard ⟨23,24,22,22,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push3_1 : PushBound ⟨23,24,22,22,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push3_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push3_2 (pattern : Twelve) : pushGuard ⟨23,24,22,22,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push3_2 : PushBound ⟨23,24,22,22,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push3_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push3_3 (pattern : Twelve) : pushGuard ⟨23,24,22,22,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push3_3 : PushBound ⟨23,24,22,22,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push3_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push4_0 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push4_1 (pattern : Twelve) : pushGuard ⟨24,23,25,25,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push4_1 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push4_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push4_2 (pattern : Twelve) : pushGuard ⟨24,23,25,25,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push4_2 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push4_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push4_3 (pattern : Twelve) : pushGuard ⟨24,23,25,25,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push4_3 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push4_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push5_0 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push5_1 (pattern : Twelve) : pushGuard ⟨24,25,23,23,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push5_1 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push5_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push5_2 (pattern : Twelve) : pushGuard ⟨24,25,23,23,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push5_2 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push5_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push5_3 (pattern : Twelve) : pushGuard ⟨24,25,23,23,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push5_3 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push5_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push6_0 : PushBound ⟨25,24,26,26,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push6_1 (pattern : Twelve) : pushGuard ⟨25,24,26,26,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push6_1 : PushBound ⟨25,24,26,26,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push6_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push6_2 (pattern : Twelve) : pushGuard ⟨25,24,26,26,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push6_2 : PushBound ⟨25,24,26,26,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push6_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push6_3 (pattern : Twelve) : pushGuard ⟨25,24,26,26,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push6_3 : PushBound ⟨25,24,26,26,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push6_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push7_0 : PushBound ⟨25,26,24,24,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push7_1 (pattern : Twelve) : pushGuard ⟨25,26,24,24,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push7_1 : PushBound ⟨25,26,24,24,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push7_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push7_2 (pattern : Twelve) : pushGuard ⟨25,26,24,24,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push7_2 : PushBound ⟨25,26,24,24,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push7_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push7_3 (pattern : Twelve) : pushGuard ⟨25,26,24,24,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push7_3 : PushBound ⟨25,26,24,24,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push7_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
end NetHack.Sokoban21
