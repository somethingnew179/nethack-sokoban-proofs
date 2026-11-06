/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers18
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk237_2 (pattern : Twelve) : walkGuard ⟨82,61,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk237_2 : WalkBound ⟨82,61,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk237_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk237_3 (pattern : Twelve) : walkGuard ⟨82,61,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk237_3 : WalkBound ⟨82,61,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk237_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_0 (pattern : Twelve) : walkGuard ⟨84,64,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk238_0 : WalkBound ⟨84,64,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_1 (pattern : Twelve) : walkGuard ⟨84,64,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk238_1 : WalkBound ⟨84,64,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_2 (pattern : Twelve) : walkGuard ⟨84,64,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk238_2 : WalkBound ⟨84,64,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_3 (pattern : Twelve) : walkGuard ⟨84,64,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk238_3 : WalkBound ⟨84,64,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_0 (pattern : Twelve) : walkGuard ⟨84,85,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk239_0 : WalkBound ⟨84,85,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_1 (pattern : Twelve) : walkGuard ⟨84,85,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk239_1 : WalkBound ⟨84,85,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_2 (pattern : Twelve) : walkGuard ⟨84,85,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk239_2 : WalkBound ⟨84,85,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_3 (pattern : Twelve) : walkGuard ⟨84,85,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk239_3 : WalkBound ⟨84,85,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_0 (pattern : Twelve) : walkGuard ⟨84,65,.northEast⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk240_0 : WalkBound ⟨84,65,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_0]; exact allowed)
  have checked := c617 pattern guarded
  change d116 pattern ≤ d351 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_1 (pattern : Twelve) : walkGuard ⟨84,65,.northEast⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk240_1 : WalkBound ⟨84,65,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_1]; exact allowed)
  have checked := c627 pattern guarded
  change d871 pattern ≤ d1017 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_2 (pattern : Twelve) : walkGuard ⟨84,65,.northEast⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk240_2 : WalkBound ⟨84,65,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_2]; exact allowed)
  have checked := c637 pattern guarded
  change d1323 pattern ≤ d1434 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_3 (pattern : Twelve) : walkGuard ⟨84,65,.northEast⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk240_3 : WalkBound ⟨84,65,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_3]; exact allowed)
  have checked := c639 pattern guarded
  change d1664 pattern ≤ d1714 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_0 (pattern : Twelve) : walkGuard ⟨84,103,.southWest⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk241_0 : WalkBound ⟨84,103,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_0]; exact allowed)
  have checked := c8858 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_1 (pattern : Twelve) : walkGuard ⟨84,103,.southWest⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk241_1 : WalkBound ⟨84,103,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_1]; exact allowed)
  have checked := c8859 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_2 (pattern : Twelve) : walkGuard ⟨84,103,.southWest⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk241_2 : WalkBound ⟨84,103,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_2]; exact allowed)
  have checked := c8860 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_3 (pattern : Twelve) : walkGuard ⟨84,103,.southWest⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk241_3 : WalkBound ⟨84,103,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_3]; exact allowed)
  have checked := c8861 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_0 (pattern : Twelve) : walkGuard ⟨85,65,.north⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk242_0 : WalkBound ⟨85,65,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_0]; exact allowed)
  have checked := c617 pattern guarded
  change d116 pattern ≤ d351 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_1 (pattern : Twelve) : walkGuard ⟨85,65,.north⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk242_1 : WalkBound ⟨85,65,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_1]; exact allowed)
  have checked := c627 pattern guarded
  change d871 pattern ≤ d1017 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_2 (pattern : Twelve) : walkGuard ⟨85,65,.north⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk242_2 : WalkBound ⟨85,65,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_2]; exact allowed)
  have checked := c637 pattern guarded
  change d1323 pattern ≤ d1434 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_3 (pattern : Twelve) : walkGuard ⟨85,65,.north⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk242_3 : WalkBound ⟨85,65,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_3]; exact allowed)
  have checked := c639 pattern guarded
  change d1664 pattern ≤ d1714 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_0 (pattern : Twelve) : walkGuard ⟨85,84,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk243_0 : WalkBound ⟨85,84,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_1 (pattern : Twelve) : walkGuard ⟨85,84,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk243_1 : WalkBound ⟨85,84,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_2 (pattern : Twelve) : walkGuard ⟨85,84,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk243_2 : WalkBound ⟨85,84,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_3 (pattern : Twelve) : walkGuard ⟨85,84,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk243_3 : WalkBound ⟨85,84,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_0 (pattern : Twelve) : walkGuard ⟨85,66,.northEast⟩ 0 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk244_0 : WalkBound ⟨85,66,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_0]; exact allowed)
  have checked := c8871 pattern guarded
  change d116 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_1 (pattern : Twelve) : walkGuard ⟨85,66,.northEast⟩ 1 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk244_1 : WalkBound ⟨85,66,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_1]; exact allowed)
  have checked := c8881 pattern guarded
  change d871 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_2 (pattern : Twelve) : walkGuard ⟨85,66,.northEast⟩ 2 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk244_2 : WalkBound ⟨85,66,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_2]; exact allowed)
  have checked := c8890 pattern guarded
  change d1323 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_3 (pattern : Twelve) : walkGuard ⟨85,66,.northEast⟩ 3 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk244_3 : WalkBound ⟨85,66,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_3]; exact allowed)
  have checked := c8892 pattern guarded
  change d1664 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk245_0 (pattern : Twelve) : walkGuard ⟨85,106,.southEast⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk245_0 : WalkBound ⟨85,106,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_0]; exact allowed)
  have checked := c8893 pattern guarded
  change d116 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk245_1 (pattern : Twelve) : walkGuard ⟨85,106,.southEast⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk245_1 : WalkBound ⟨85,106,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_1]; exact allowed)
  have checked := c8894 pattern guarded
  change d871 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk245_2 (pattern : Twelve) : walkGuard ⟨85,106,.southEast⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk245_2 : WalkBound ⟨85,106,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_2]; exact allowed)
  have checked := c8895 pattern guarded
  change d1323 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk245_3 (pattern : Twelve) : walkGuard ⟨85,106,.southEast⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk245_3 : WalkBound ⟨85,106,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk245_3]; exact allowed)
  have checked := c8896 pattern guarded
  change d1664 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_0 (pattern : Twelve) : walkGuard ⟨85,64,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk246_0 : WalkBound ⟨85,64,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_1 (pattern : Twelve) : walkGuard ⟨85,64,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk246_1 : WalkBound ⟨85,64,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_2 (pattern : Twelve) : walkGuard ⟨85,64,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk246_2 : WalkBound ⟨85,64,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk246_3 (pattern : Twelve) : walkGuard ⟨85,64,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk246_3 : WalkBound ⟨85,64,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk246_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_0 (pattern : Twelve) : walkGuard ⟨87,67,.north⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk247_0 : WalkBound ⟨87,67,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_0]; exact allowed)
  have checked := c8970 pattern guarded
  change d156 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_1 (pattern : Twelve) : walkGuard ⟨87,67,.north⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk247_1 : WalkBound ⟨87,67,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_1]; exact allowed)
  have checked := c9030 pattern guarded
  change d907 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_2 (pattern : Twelve) : walkGuard ⟨87,67,.north⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk247_2 : WalkBound ⟨87,67,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_2]; exact allowed)
  have checked := c9076 pattern guarded
  change d1354 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk247_3 (pattern : Twelve) : walkGuard ⟨87,67,.north⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk247_3 : WalkBound ⟨87,67,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk247_3]; exact allowed)
  have checked := c9103 pattern guarded
  change d1678 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_0 (pattern : Twelve) : walkGuard ⟨87,88,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk248_0 : WalkBound ⟨87,88,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_1 (pattern : Twelve) : walkGuard ⟨87,88,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk248_1 : WalkBound ⟨87,88,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_2 (pattern : Twelve) : walkGuard ⟨87,88,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk248_2 : WalkBound ⟨87,88,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk248_3 (pattern : Twelve) : walkGuard ⟨87,88,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk248_3 : WalkBound ⟨87,88,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk248_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_0 (pattern : Twelve) : walkGuard ⟨87,107,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk249_0 : WalkBound ⟨87,107,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_1 (pattern : Twelve) : walkGuard ⟨87,107,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk249_1 : WalkBound ⟨87,107,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_2 (pattern : Twelve) : walkGuard ⟨87,107,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk249_2 : WalkBound ⟨87,107,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk249_3 (pattern : Twelve) : walkGuard ⟨87,107,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk249_3 : WalkBound ⟨87,107,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk249_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
