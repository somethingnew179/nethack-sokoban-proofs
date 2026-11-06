/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers59
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem push108_0 : PushBound ⟨95,115,75,75,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push108_1 (pattern : Twelve) : pushGuard ⟨95,115,75,75,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push108_1 : PushBound ⟨95,115,75,75,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push108_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push108_2 (pattern : Twelve) : pushGuard ⟨95,115,75,75,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push108_2 : PushBound ⟨95,115,75,75,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push108_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push108_3 (pattern : Twelve) : pushGuard ⟨95,115,75,75,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push108_3 : PushBound ⟨95,115,75,75,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push108_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push109_0 : PushBound ⟨95,94,96,96,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push109_1 (pattern : Twelve) : pushGuard ⟨95,94,96,96,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push109_1 : PushBound ⟨95,94,96,96,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push109_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push109_2 (pattern : Twelve) : pushGuard ⟨95,94,96,96,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push109_2 : PushBound ⟨95,94,96,96,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push109_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push109_3 (pattern : Twelve) : pushGuard ⟨95,94,96,96,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push109_3 : PushBound ⟨95,94,96,96,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push109_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push110_0 : PushBound ⟨95,75,115,115,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push110_1 (pattern : Twelve) : pushGuard ⟨95,75,115,115,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push110_1 : PushBound ⟨95,75,115,115,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push110_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push110_2 (pattern : Twelve) : pushGuard ⟨95,75,115,115,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push110_2 : PushBound ⟨95,75,115,115,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push110_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push110_3 (pattern : Twelve) : pushGuard ⟨95,75,115,115,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push110_3 : PushBound ⟨95,75,115,115,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push110_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push111_0 : PushBound ⟨95,96,94,94,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push111_1 (pattern : Twelve) : pushGuard ⟨95,96,94,94,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push111_1 : PushBound ⟨95,96,94,94,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push111_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push111_2 (pattern : Twelve) : pushGuard ⟨95,96,94,94,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push111_2 : PushBound ⟨95,96,94,94,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push111_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push111_3 (pattern : Twelve) : pushGuard ⟨95,96,94,94,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push111_3 : PushBound ⟨95,96,94,94,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push111_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push112_0 : PushBound ⟨96,116,76,76,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push112_1 (pattern : Twelve) : pushGuard ⟨96,116,76,76,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push112_1 : PushBound ⟨96,116,76,76,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push112_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push112_2 (pattern : Twelve) : pushGuard ⟨96,116,76,76,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push112_2 : PushBound ⟨96,116,76,76,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push112_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push112_3 (pattern : Twelve) : pushGuard ⟨96,116,76,76,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push112_3 : PushBound ⟨96,116,76,76,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push112_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push113_0 : PushBound ⟨96,95,97,97,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push113_1 (pattern : Twelve) : pushGuard ⟨96,95,97,97,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push113_1 : PushBound ⟨96,95,97,97,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push113_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push113_2 (pattern : Twelve) : pushGuard ⟨96,95,97,97,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push113_2 : PushBound ⟨96,95,97,97,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push113_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push113_3 (pattern : Twelve) : pushGuard ⟨96,95,97,97,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push113_3 : PushBound ⟨96,95,97,97,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push113_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push114_0 : PushBound ⟨96,76,116,116,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push114_1 (pattern : Twelve) : pushGuard ⟨96,76,116,116,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push114_1 : PushBound ⟨96,76,116,116,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push114_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push114_2 (pattern : Twelve) : pushGuard ⟨96,76,116,116,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push114_2 : PushBound ⟨96,76,116,116,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push114_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push114_3 (pattern : Twelve) : pushGuard ⟨96,76,116,116,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push114_3 : PushBound ⟨96,76,116,116,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push114_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push115_0 : PushBound ⟨96,97,95,95,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push115_1 (pattern : Twelve) : pushGuard ⟨96,97,95,95,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push115_1 : PushBound ⟨96,97,95,95,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push115_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push115_2 (pattern : Twelve) : pushGuard ⟨96,97,95,95,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push115_2 : PushBound ⟨96,97,95,95,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push115_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push115_3 (pattern : Twelve) : pushGuard ⟨96,97,95,95,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push115_3 : PushBound ⟨96,97,95,95,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push115_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push116_0 : PushBound ⟨97,117,77,77,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push116_1 (pattern : Twelve) : pushGuard ⟨97,117,77,77,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push116_1 : PushBound ⟨97,117,77,77,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push116_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push116_2 (pattern : Twelve) : pushGuard ⟨97,117,77,77,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push116_2 : PushBound ⟨97,117,77,77,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push116_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push116_3 (pattern : Twelve) : pushGuard ⟨97,117,77,77,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push116_3 : PushBound ⟨97,117,77,77,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push116_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push117_0 : PushBound ⟨97,96,98,98,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push117_1 (pattern : Twelve) : pushGuard ⟨97,96,98,98,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push117_1 : PushBound ⟨97,96,98,98,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push117_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push117_2 (pattern : Twelve) : pushGuard ⟨97,96,98,98,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push117_2 : PushBound ⟨97,96,98,98,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push117_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push117_3 (pattern : Twelve) : pushGuard ⟨97,96,98,98,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push117_3 : PushBound ⟨97,96,98,98,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push117_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push118_0 : PushBound ⟨97,77,117,117,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push118_1 (pattern : Twelve) : pushGuard ⟨97,77,117,117,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push118_1 : PushBound ⟨97,77,117,117,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push118_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push118_2 (pattern : Twelve) : pushGuard ⟨97,77,117,117,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push118_2 : PushBound ⟨97,77,117,117,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push118_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push118_3 (pattern : Twelve) : pushGuard ⟨97,77,117,117,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push118_3 : PushBound ⟨97,77,117,117,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push118_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push119_0 : PushBound ⟨97,98,96,96,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push119_1 (pattern : Twelve) : pushGuard ⟨97,98,96,96,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push119_1 : PushBound ⟨97,98,96,96,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push119_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push119_2 (pattern : Twelve) : pushGuard ⟨97,98,96,96,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push119_2 : PushBound ⟨97,98,96,96,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push119_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push119_3 (pattern : Twelve) : pushGuard ⟨97,98,96,96,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push119_3 : PushBound ⟨97,98,96,96,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push119_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push120_0 : PushBound ⟨98,118,78,78,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push120_1 (pattern : Twelve) : pushGuard ⟨98,118,78,78,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push120_1 : PushBound ⟨98,118,78,78,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push120_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
end NetHack.Sokoban21
