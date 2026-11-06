/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers47
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk600_0 (pattern : Twelve) : walkGuard ⟨187,166,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk600_0 : WalkBound ⟨187,166,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk600_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk600_1 (pattern : Twelve) : walkGuard ⟨187,166,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk600_1 : WalkBound ⟨187,166,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk600_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk600_2 (pattern : Twelve) : walkGuard ⟨187,166,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk600_2 : WalkBound ⟨187,166,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk600_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk600_3 (pattern : Twelve) : walkGuard ⟨187,166,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk600_3 : WalkBound ⟨187,166,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk600_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk601_0 (pattern : Twelve) : walkGuard ⟨188,189,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk601_0 : WalkBound ⟨188,189,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk601_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk601_1 (pattern : Twelve) : walkGuard ⟨188,189,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk601_1 : WalkBound ⟨188,189,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk601_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk601_2 (pattern : Twelve) : walkGuard ⟨188,189,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk601_2 : WalkBound ⟨188,189,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk601_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk601_3 (pattern : Twelve) : walkGuard ⟨188,189,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk601_3 : WalkBound ⟨188,189,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk601_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk602_0 (pattern : Twelve) : walkGuard ⟨188,187,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk602_0 : WalkBound ⟨188,187,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk602_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk602_1 (pattern : Twelve) : walkGuard ⟨188,187,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk602_1 : WalkBound ⟨188,187,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk602_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk602_2 (pattern : Twelve) : walkGuard ⟨188,187,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk602_2 : WalkBound ⟨188,187,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk602_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk602_3 (pattern : Twelve) : walkGuard ⟨188,187,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk602_3 : WalkBound ⟨188,187,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk602_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk603_0 (pattern : Twelve) : walkGuard ⟨189,190,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk603_0 : WalkBound ⟨189,190,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk603_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk603_1 (pattern : Twelve) : walkGuard ⟨189,190,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk603_1 : WalkBound ⟨189,190,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk603_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk603_2 (pattern : Twelve) : walkGuard ⟨189,190,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk603_2 : WalkBound ⟨189,190,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk603_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk603_3 (pattern : Twelve) : walkGuard ⟨189,190,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk603_3 : WalkBound ⟨189,190,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk603_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk604_0 (pattern : Twelve) : walkGuard ⟨189,188,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk604_0 : WalkBound ⟨189,188,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk604_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk604_1 (pattern : Twelve) : walkGuard ⟨189,188,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk604_1 : WalkBound ⟨189,188,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk604_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk604_2 (pattern : Twelve) : walkGuard ⟨189,188,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk604_2 : WalkBound ⟨189,188,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk604_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk604_3 (pattern : Twelve) : walkGuard ⟨189,188,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk604_3 : WalkBound ⟨189,188,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk604_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk605_0 (pattern : Twelve) : walkGuard ⟨190,191,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk605_0 : WalkBound ⟨190,191,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk605_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk605_1 (pattern : Twelve) : walkGuard ⟨190,191,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk605_1 : WalkBound ⟨190,191,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk605_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk605_2 (pattern : Twelve) : walkGuard ⟨190,191,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk605_2 : WalkBound ⟨190,191,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk605_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk605_3 (pattern : Twelve) : walkGuard ⟨190,191,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk605_3 : WalkBound ⟨190,191,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk605_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk606_0 (pattern : Twelve) : walkGuard ⟨190,189,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk606_0 : WalkBound ⟨190,189,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk606_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk606_1 (pattern : Twelve) : walkGuard ⟨190,189,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk606_1 : WalkBound ⟨190,189,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk606_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk606_2 (pattern : Twelve) : walkGuard ⟨190,189,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk606_2 : WalkBound ⟨190,189,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk606_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk606_3 (pattern : Twelve) : walkGuard ⟨190,189,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk606_3 : WalkBound ⟨190,189,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk606_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk607_0 (pattern : Twelve) : walkGuard ⟨191,192,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk607_0 : WalkBound ⟨191,192,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk607_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk607_1 (pattern : Twelve) : walkGuard ⟨191,192,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk607_1 : WalkBound ⟨191,192,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk607_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk607_2 (pattern : Twelve) : walkGuard ⟨191,192,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk607_2 : WalkBound ⟨191,192,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk607_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk607_3 (pattern : Twelve) : walkGuard ⟨191,192,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk607_3 : WalkBound ⟨191,192,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk607_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk608_0 (pattern : Twelve) : walkGuard ⟨191,190,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk608_0 : WalkBound ⟨191,190,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk608_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk608_1 (pattern : Twelve) : walkGuard ⟨191,190,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk608_1 : WalkBound ⟨191,190,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk608_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk608_2 (pattern : Twelve) : walkGuard ⟨191,190,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk608_2 : WalkBound ⟨191,190,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk608_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk608_3 (pattern : Twelve) : walkGuard ⟨191,190,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk608_3 : WalkBound ⟨191,190,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk608_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk609_0 (pattern : Twelve) : walkGuard ⟨192,193,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk609_0 : WalkBound ⟨192,193,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk609_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk609_1 (pattern : Twelve) : walkGuard ⟨192,193,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk609_1 : WalkBound ⟨192,193,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk609_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk609_2 (pattern : Twelve) : walkGuard ⟨192,193,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk609_2 : WalkBound ⟨192,193,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk609_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk609_3 (pattern : Twelve) : walkGuard ⟨192,193,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk609_3 : WalkBound ⟨192,193,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk609_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk610_0 (pattern : Twelve) : walkGuard ⟨192,191,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk610_0 : WalkBound ⟨192,191,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk610_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk610_1 (pattern : Twelve) : walkGuard ⟨192,191,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk610_1 : WalkBound ⟨192,191,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk610_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk610_2 (pattern : Twelve) : walkGuard ⟨192,191,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk610_2 : WalkBound ⟨192,191,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk610_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk610_3 (pattern : Twelve) : walkGuard ⟨192,191,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk610_3 : WalkBound ⟨192,191,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk610_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk611_0 (pattern : Twelve) : walkGuard ⟨193,194,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk611_0 : WalkBound ⟨193,194,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk611_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk611_1 (pattern : Twelve) : walkGuard ⟨193,194,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk611_1 : WalkBound ⟨193,194,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk611_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk611_2 (pattern : Twelve) : walkGuard ⟨193,194,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk611_2 : WalkBound ⟨193,194,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk611_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk611_3 (pattern : Twelve) : walkGuard ⟨193,194,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk611_3 : WalkBound ⟨193,194,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk611_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk612_0 (pattern : Twelve) : walkGuard ⟨193,192,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk612_0 : WalkBound ⟨193,192,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk612_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk612_1 (pattern : Twelve) : walkGuard ⟨193,192,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk612_1 : WalkBound ⟨193,192,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk612_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
