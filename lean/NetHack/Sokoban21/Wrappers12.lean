/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers11
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk150_0 (pattern : Twelve) : walkGuard ⟨61,62,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk150_0 : WalkBound ⟨61,62,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk150_1 (pattern : Twelve) : walkGuard ⟨61,62,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk150_1 : WalkBound ⟨61,62,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk150_2 (pattern : Twelve) : walkGuard ⟨61,62,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk150_2 : WalkBound ⟨61,62,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk150_3 (pattern : Twelve) : walkGuard ⟨61,62,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk150_3 : WalkBound ⟨61,62,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_0 (pattern : Twelve) : walkGuard ⟨61,42,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk151_0 : WalkBound ⟨61,42,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_1 (pattern : Twelve) : walkGuard ⟨61,42,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk151_1 : WalkBound ⟨61,42,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_2 (pattern : Twelve) : walkGuard ⟨61,42,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk151_2 : WalkBound ⟨61,42,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_3 (pattern : Twelve) : walkGuard ⟨61,42,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk151_3 : WalkBound ⟨61,42,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_0 (pattern : Twelve) : walkGuard ⟨61,82,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk152_0 : WalkBound ⟨61,82,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_1 (pattern : Twelve) : walkGuard ⟨61,82,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk152_1 : WalkBound ⟨61,82,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_2 (pattern : Twelve) : walkGuard ⟨61,82,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk152_2 : WalkBound ⟨61,82,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_3 (pattern : Twelve) : walkGuard ⟨61,82,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk152_3 : WalkBound ⟨61,82,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_0 (pattern : Twelve) : walkGuard ⟨62,42,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk153_0 : WalkBound ⟨62,42,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_1 (pattern : Twelve) : walkGuard ⟨62,42,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk153_1 : WalkBound ⟨62,42,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_2 (pattern : Twelve) : walkGuard ⟨62,42,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk153_2 : WalkBound ⟨62,42,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_3 (pattern : Twelve) : walkGuard ⟨62,42,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk153_3 : WalkBound ⟨62,42,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_0 (pattern : Twelve) : walkGuard ⟨62,82,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk154_0 : WalkBound ⟨62,82,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_1 (pattern : Twelve) : walkGuard ⟨62,82,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk154_1 : WalkBound ⟨62,82,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_2 (pattern : Twelve) : walkGuard ⟨62,82,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk154_2 : WalkBound ⟨62,82,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_3 (pattern : Twelve) : walkGuard ⟨62,82,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk154_3 : WalkBound ⟨62,82,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_0 (pattern : Twelve) : walkGuard ⟨62,61,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk155_0 : WalkBound ⟨62,61,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_1 (pattern : Twelve) : walkGuard ⟨62,61,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk155_1 : WalkBound ⟨62,61,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_2 (pattern : Twelve) : walkGuard ⟨62,61,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk155_2 : WalkBound ⟨62,61,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_3 (pattern : Twelve) : walkGuard ⟨62,61,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk155_3 : WalkBound ⟨62,61,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_0 (pattern : Twelve) : walkGuard ⟨62,43,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk156_0 : WalkBound ⟨62,43,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_1 (pattern : Twelve) : walkGuard ⟨62,43,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk156_1 : WalkBound ⟨62,43,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_2 (pattern : Twelve) : walkGuard ⟨62,43,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk156_2 : WalkBound ⟨62,43,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_3 (pattern : Twelve) : walkGuard ⟨62,43,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk156_3 : WalkBound ⟨62,43,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_0 (pattern : Twelve) : walkGuard ⟨62,41,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk157_0 : WalkBound ⟨62,41,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_1 (pattern : Twelve) : walkGuard ⟨62,41,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk157_1 : WalkBound ⟨62,41,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_2 (pattern : Twelve) : walkGuard ⟨62,41,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk157_2 : WalkBound ⟨62,41,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_3 (pattern : Twelve) : walkGuard ⟨62,41,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk157_3 : WalkBound ⟨62,41,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_0 (pattern : Twelve) : walkGuard ⟨64,44,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk158_0 : WalkBound ⟨64,44,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_1 (pattern : Twelve) : walkGuard ⟨64,44,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk158_1 : WalkBound ⟨64,44,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_2 (pattern : Twelve) : walkGuard ⟨64,44,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk158_2 : WalkBound ⟨64,44,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_3 (pattern : Twelve) : walkGuard ⟨64,44,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk158_3 : WalkBound ⟨64,44,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_0 (pattern : Twelve) : walkGuard ⟨64,65,.east⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk159_0 : WalkBound ⟨64,65,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_0]; exact allowed)
  have checked := c617 pattern guarded
  change d116 pattern ≤ d351 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_1 (pattern : Twelve) : walkGuard ⟨64,65,.east⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk159_1 : WalkBound ⟨64,65,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_1]; exact allowed)
  have checked := c627 pattern guarded
  change d871 pattern ≤ d1017 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_2 (pattern : Twelve) : walkGuard ⟨64,65,.east⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk159_2 : WalkBound ⟨64,65,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_2]; exact allowed)
  have checked := c637 pattern guarded
  change d1323 pattern ≤ d1434 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_3 (pattern : Twelve) : walkGuard ⟨64,65,.east⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk159_3 : WalkBound ⟨64,65,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_3]; exact allowed)
  have checked := c639 pattern guarded
  change d1664 pattern ≤ d1714 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_0 (pattern : Twelve) : walkGuard ⟨64,84,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk160_0 : WalkBound ⟨64,84,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_1 (pattern : Twelve) : walkGuard ⟨64,84,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk160_1 : WalkBound ⟨64,84,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_2 (pattern : Twelve) : walkGuard ⟨64,84,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk160_2 : WalkBound ⟨64,84,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_3 (pattern : Twelve) : walkGuard ⟨64,84,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk160_3 : WalkBound ⟨64,84,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_0 (pattern : Twelve) : walkGuard ⟨64,45,.northEast⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk161_0 : WalkBound ⟨64,45,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_0]; exact allowed)
  have checked := c26 pattern guarded
  change d116 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_1 (pattern : Twelve) : walkGuard ⟨64,45,.northEast⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk161_1 : WalkBound ⟨64,45,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_1]; exact allowed)
  have checked := c49 pattern guarded
  change d871 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_2 (pattern : Twelve) : walkGuard ⟨64,45,.northEast⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk161_2 : WalkBound ⟨64,45,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_2]; exact allowed)
  have checked := c70 pattern guarded
  change d1323 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_3 (pattern : Twelve) : walkGuard ⟨64,45,.northEast⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk161_3 : WalkBound ⟨64,45,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_3]; exact allowed)
  have checked := c77 pattern guarded
  change d1664 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk162_0 (pattern : Twelve) : walkGuard ⟨64,85,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk162_0 : WalkBound ⟨64,85,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk162_1 (pattern : Twelve) : walkGuard ⟨64,85,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk162_1 : WalkBound ⟨64,85,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
