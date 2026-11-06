/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers52
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push20_2 (pattern : Twelve) : pushGuard ⟨41,61,21,21,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push20_2 : PushBound ⟨41,61,21,21,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push20_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push20_3 (pattern : Twelve) : pushGuard ⟨41,61,21,21,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push20_3 : PushBound ⟨41,61,21,21,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push20_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem push21_0 : PushBound ⟨41,21,61,61,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push21_1 (pattern : Twelve) : pushGuard ⟨41,21,61,61,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push21_1 : PushBound ⟨41,21,61,61,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push21_1]; exact allowed)
  have checked := c9808 pattern guarded
  change d871 pattern ≤ (1 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push21_2 (pattern : Twelve) : pushGuard ⟨41,21,61,61,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push21_2 : PushBound ⟨41,21,61,61,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push21_2]; exact allowed)
  have checked := c9809 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push21_3 (pattern : Twelve) : pushGuard ⟨41,21,61,61,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push21_3 : PushBound ⟨41,21,61,61,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push21_3]; exact allowed)
  have checked := c9810 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push22_0 (pattern : Twelve) : pushGuard ⟨42,62,22,22,.north,8,8,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push22_0 : PushBound ⟨42,62,22,22,.north,8,8,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_0]; exact allowed)
  have checked := c9965 pattern guarded
  change d116 pattern ≤ (8 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push22_1 (pattern : Twelve) : pushGuard ⟨42,62,22,22,.north,8,8,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push22_1 : PushBound ⟨42,62,22,22,.north,8,8,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_1]; exact allowed)
  have checked := c10050 pattern guarded
  change d871 pattern ≤ (8 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push22_2 (pattern : Twelve) : pushGuard ⟨42,62,22,22,.north,8,8,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push22_2 : PushBound ⟨42,62,22,22,.north,8,8,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_2]; exact allowed)
  have checked := c10107 pattern guarded
  change d1323 pattern ≤ (8 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push22_3 (pattern : Twelve) : pushGuard ⟨42,62,22,22,.north,8,8,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push22_3 : PushBound ⟨42,62,22,22,.north,8,8,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_3]; exact allowed)
  have checked := c10134 pattern guarded
  change d1664 pattern ≤ (8 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push23_0 (pattern : Twelve) : pushGuard ⟨42,41,43,43,.east,2,8,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push23_0 : PushBound ⟨42,41,43,43,.east,2,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push23_1 (pattern : Twelve) : pushGuard ⟨42,41,43,43,.east,2,8,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push23_1 : PushBound ⟨42,41,43,43,.east,2,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push23_2 (pattern : Twelve) : pushGuard ⟨42,41,43,43,.east,2,8,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push23_2 : PushBound ⟨42,41,43,43,.east,2,8,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push23_3 (pattern : Twelve) : pushGuard ⟨42,41,43,43,.east,2,8,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push23_3 : PushBound ⟨42,41,43,43,.east,2,8,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push24_0 (pattern : Twelve) : pushGuard ⟨42,22,62,62,.south,0,8,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push24_0 : PushBound ⟨42,22,62,62,.south,0,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push24_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push24_1 (pattern : Twelve) : pushGuard ⟨42,22,62,62,.south,0,8,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push24_1 : PushBound ⟨42,22,62,62,.south,0,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push24_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push24_2 (pattern : Twelve) : pushGuard ⟨42,22,62,62,.south,0,8,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push24_2 : PushBound ⟨42,22,62,62,.south,0,8,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push24_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push24_3 (pattern : Twelve) : pushGuard ⟨42,22,62,62,.south,0,8,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push24_3 : PushBound ⟨42,22,62,62,.south,0,8,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push24_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push25_0 (pattern : Twelve) : pushGuard ⟨42,43,41,41,.west,8,8,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push25_0 : PushBound ⟨42,43,41,41,.west,8,8,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push25_0]; exact allowed)
  have checked := c9965 pattern guarded
  change d116 pattern ≤ (8 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push25_1 (pattern : Twelve) : pushGuard ⟨42,43,41,41,.west,8,8,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push25_1 : PushBound ⟨42,43,41,41,.west,8,8,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push25_1]; exact allowed)
  have checked := c10050 pattern guarded
  change d871 pattern ≤ (8 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push25_2 (pattern : Twelve) : pushGuard ⟨42,43,41,41,.west,8,8,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push25_2 : PushBound ⟨42,43,41,41,.west,8,8,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push25_2]; exact allowed)
  have checked := c10107 pattern guarded
  change d1323 pattern ≤ (8 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push25_3 (pattern : Twelve) : pushGuard ⟨42,43,41,41,.west,8,8,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push25_3 : PushBound ⟨42,43,41,41,.west,8,8,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push25_3]; exact allowed)
  have checked := c10134 pattern guarded
  change d1664 pattern ≤ (8 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push26_0 (pattern : Twelve) : pushGuard ⟨43,42,44,44,.east,2,7,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push26_0 : PushBound ⟨43,42,44,44,.east,2,7,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push26_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push26_1 (pattern : Twelve) : pushGuard ⟨43,42,44,44,.east,2,7,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push26_1 : PushBound ⟨43,42,44,44,.east,2,7,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push26_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push26_2 (pattern : Twelve) : pushGuard ⟨43,42,44,44,.east,2,7,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push26_2 : PushBound ⟨43,42,44,44,.east,2,7,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push26_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push26_3 (pattern : Twelve) : pushGuard ⟨43,42,44,44,.east,2,7,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push26_3 : PushBound ⟨43,42,44,44,.east,2,7,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push26_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push27_0 (pattern : Twelve) : pushGuard ⟨43,44,42,42,.west,0,7,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push27_0 : PushBound ⟨43,44,42,42,.west,0,7,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push27_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push27_1 (pattern : Twelve) : pushGuard ⟨43,44,42,42,.west,0,7,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push27_1 : PushBound ⟨43,44,42,42,.west,0,7,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push27_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push27_2 (pattern : Twelve) : pushGuard ⟨43,44,42,42,.west,0,7,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push27_2 : PushBound ⟨43,44,42,42,.west,0,7,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push27_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push27_3 (pattern : Twelve) : pushGuard ⟨43,44,42,42,.west,0,7,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push27_3 : PushBound ⟨43,44,42,42,.west,0,7,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push27_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push28_0 (pattern : Twelve) : pushGuard ⟨44,64,24,24,.north,6,6,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push28_0 : PushBound ⟨44,64,24,24,.north,6,6,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_0]; exact allowed)
  have checked := c10287 pattern guarded
  change d116 pattern ≤ (6 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push28_1 (pattern : Twelve) : pushGuard ⟨44,64,24,24,.north,6,6,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push28_1 : PushBound ⟨44,64,24,24,.north,6,6,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_1]; exact allowed)
  have checked := c10372 pattern guarded
  change d871 pattern ≤ (6 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push28_2 (pattern : Twelve) : pushGuard ⟨44,64,24,24,.north,6,6,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push28_2 : PushBound ⟨44,64,24,24,.north,6,6,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_2]; exact allowed)
  have checked := c10429 pattern guarded
  change d1323 pattern ≤ (6 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push28_3 (pattern : Twelve) : pushGuard ⟨44,64,24,24,.north,6,6,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push28_3 : PushBound ⟨44,64,24,24,.north,6,6,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_3]; exact allowed)
  have checked := c10456 pattern guarded
  change d1664 pattern ≤ (6 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push29_0 (pattern : Twelve) : pushGuard ⟨44,43,45,45,.east,4,6,false,false⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push29_0 : PushBound ⟨44,43,45,45,.east,4,6,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_0]; exact allowed)
  have checked := c10556 pattern guarded
  change d116 pattern ≤ (4 : Int) + d116 (change pattern 12 3)
  rw [s458]
  exact checked
theorem guard_push29_1 (pattern : Twelve) : pushGuard ⟨44,43,45,45,.east,4,6,false,false⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push29_1 : PushBound ⟨44,43,45,45,.east,4,6,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_1]; exact allowed)
  have checked := c10597 pattern guarded
  change d871 pattern ≤ (4 : Int) + d871 (change pattern 12 3)
  rw [s495]
  exact checked
theorem guard_push29_2 (pattern : Twelve) : pushGuard ⟨44,43,45,45,.east,4,6,false,false⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push29_2 : PushBound ⟨44,43,45,45,.east,4,6,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_2]; exact allowed)
  have checked := c10638 pattern guarded
  change d1323 pattern ≤ (4 : Int) + d1323 (change pattern 12 3)
  rw [s527]
  exact checked
theorem guard_push29_3 (pattern : Twelve) : pushGuard ⟨44,43,45,45,.east,4,6,false,false⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push29_3 : PushBound ⟨44,43,45,45,.east,4,6,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_3]; exact allowed)
  have checked := c10660 pattern guarded
  change d1664 pattern ≤ (4 : Int) + d1664 (change pattern 12 3)
  rw [s547]
  exact checked
theorem guard_push30_0 (pattern : Twelve) : pushGuard ⟨44,24,64,64,.south,2,6,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push30_0 : PushBound ⟨44,24,64,64,.south,2,6,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push30_1 (pattern : Twelve) : pushGuard ⟨44,24,64,64,.south,2,6,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push30_1 : PushBound ⟨44,24,64,64,.south,2,6,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push30_2 (pattern : Twelve) : pushGuard ⟨44,24,64,64,.south,2,6,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push30_2 : PushBound ⟨44,24,64,64,.south,2,6,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push30_3 (pattern : Twelve) : pushGuard ⟨44,24,64,64,.south,2,6,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push30_3 : PushBound ⟨44,24,64,64,.south,2,6,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push31_0 (pattern : Twelve) : pushGuard ⟨44,45,43,43,.west,0,6,false,false⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push31_0 : PushBound ⟨44,45,43,43,.west,0,6,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push31_1 (pattern : Twelve) : pushGuard ⟨44,45,43,43,.west,0,6,false,false⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push31_1 : PushBound ⟨44,45,43,43,.west,0,6,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push31_2 (pattern : Twelve) : pushGuard ⟨44,45,43,43,.west,0,6,false,false⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push31_2 : PushBound ⟨44,45,43,43,.west,0,6,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push31_3 (pattern : Twelve) : pushGuard ⟨44,45,43,43,.west,0,6,false,false⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem push31_3 : PushBound ⟨44,45,43,43,.west,0,6,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push32_0 (pattern : Twelve) : pushGuard ⟨45,65,25,25,.north,3,3,false,true⟩ 0 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push32_0 : PushBound ⟨45,65,25,25,.north,3,3,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_0]; exact allowed)
  have checked := c10731 pattern guarded
  change d351 pattern ≤ (3 : Int) + d939 (change pattern 3 12)
  rw [s649]
  exact checked
theorem guard_push32_1 (pattern : Twelve) : pushGuard ⟨45,65,25,25,.north,3,3,false,true⟩ 1 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push32_1 : PushBound ⟨45,65,25,25,.north,3,3,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_1]; exact allowed)
  have checked := c10795 pattern guarded
  change d1017 pattern ≤ (3 : Int) + d1379 (change pattern 3 12)
  rw [s710]
  exact checked
theorem guard_push32_2 (pattern : Twelve) : pushGuard ⟨45,65,25,25,.north,3,3,false,true⟩ 2 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push32_2 : PushBound ⟨45,65,25,25,.north,3,3,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_2]; exact allowed)
  have checked := c10838 pattern guarded
  change d1434 pattern ≤ (3 : Int) + d1688 (change pattern 3 12)
  rw [s735]
  exact checked
theorem guard_push32_3 (pattern : Twelve) : pushGuard ⟨45,65,25,25,.north,3,3,false,true⟩ 3 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push32_3 : PushBound ⟨45,65,25,25,.north,3,3,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_3]; exact allowed)
  have checked := c10861 pattern guarded
  change d1714 pattern ≤ (3 : Int) + d6 (change pattern 3 12)
  rw [s568]
  exact checked
end NetHack.Sokoban21
