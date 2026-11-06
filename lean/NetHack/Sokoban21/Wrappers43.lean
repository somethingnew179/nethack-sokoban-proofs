/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers42
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk537_2 (pattern : Twelve) : walkGuard ⟨162,142,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk537_2 : WalkBound ⟨162,142,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk537_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk537_3 (pattern : Twelve) : walkGuard ⟨162,142,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk537_3 : WalkBound ⟨162,142,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk537_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk538_0 (pattern : Twelve) : walkGuard ⟨162,163,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk538_0 : WalkBound ⟨162,163,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk538_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk538_1 (pattern : Twelve) : walkGuard ⟨162,163,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk538_1 : WalkBound ⟨162,163,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk538_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk538_2 (pattern : Twelve) : walkGuard ⟨162,163,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk538_2 : WalkBound ⟨162,163,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk538_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk538_3 (pattern : Twelve) : walkGuard ⟨162,163,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk538_3 : WalkBound ⟨162,163,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk538_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk539_0 (pattern : Twelve) : walkGuard ⟨162,182,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk539_0 : WalkBound ⟨162,182,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk539_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk539_1 (pattern : Twelve) : walkGuard ⟨162,182,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk539_1 : WalkBound ⟨162,182,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk539_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk539_2 (pattern : Twelve) : walkGuard ⟨162,182,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk539_2 : WalkBound ⟨162,182,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk539_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk539_3 (pattern : Twelve) : walkGuard ⟨162,182,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk539_3 : WalkBound ⟨162,182,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk539_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk540_0 (pattern : Twelve) : walkGuard ⟨162,143,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk540_0 : WalkBound ⟨162,143,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk540_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk540_1 (pattern : Twelve) : walkGuard ⟨162,143,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk540_1 : WalkBound ⟨162,143,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk540_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk540_2 (pattern : Twelve) : walkGuard ⟨162,143,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk540_2 : WalkBound ⟨162,143,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk540_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk540_3 (pattern : Twelve) : walkGuard ⟨162,143,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk540_3 : WalkBound ⟨162,143,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk540_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk541_0 (pattern : Twelve) : walkGuard ⟨162,183,.southEast⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk541_0 : WalkBound ⟨162,183,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk541_0]; exact allowed)
  have checked := c9776 pattern guarded
  change d116 pattern ≤ d813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk541_1 (pattern : Twelve) : walkGuard ⟨162,183,.southEast⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk541_1 : WalkBound ⟨162,183,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk541_1]; exact allowed)
  have checked := c9777 pattern guarded
  change d871 pattern ≤ d1274 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk541_2 (pattern : Twelve) : walkGuard ⟨162,183,.southEast⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk541_2 : WalkBound ⟨162,183,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk541_2]; exact allowed)
  have checked := c9778 pattern guarded
  change d1323 pattern ≤ d1643 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk541_3 (pattern : Twelve) : walkGuard ⟨162,183,.southEast⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk541_3 : WalkBound ⟨162,183,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk541_3]; exact allowed)
  have checked := c9779 pattern guarded
  change d1664 pattern ≤ d1834 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk542_0 (pattern : Twelve) : walkGuard ⟨162,181,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk542_0 : WalkBound ⟨162,181,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk542_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk542_1 (pattern : Twelve) : walkGuard ⟨162,181,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk542_1 : WalkBound ⟨162,181,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk542_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk542_2 (pattern : Twelve) : walkGuard ⟨162,181,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk542_2 : WalkBound ⟨162,181,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk542_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk542_3 (pattern : Twelve) : walkGuard ⟨162,181,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk542_3 : WalkBound ⟨162,181,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk542_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk543_0 (pattern : Twelve) : walkGuard ⟨162,141,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk543_0 : WalkBound ⟨162,141,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk543_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk543_1 (pattern : Twelve) : walkGuard ⟨162,141,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk543_1 : WalkBound ⟨162,141,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk543_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk543_2 (pattern : Twelve) : walkGuard ⟨162,141,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk543_2 : WalkBound ⟨162,141,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk543_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk543_3 (pattern : Twelve) : walkGuard ⟨162,141,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk543_3 : WalkBound ⟨162,141,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk543_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk544_0 (pattern : Twelve) : walkGuard ⟨163,143,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk544_0 : WalkBound ⟨163,143,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk544_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk544_1 (pattern : Twelve) : walkGuard ⟨163,143,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk544_1 : WalkBound ⟨163,143,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk544_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk544_2 (pattern : Twelve) : walkGuard ⟨163,143,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk544_2 : WalkBound ⟨163,143,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk544_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk544_3 (pattern : Twelve) : walkGuard ⟨163,143,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk544_3 : WalkBound ⟨163,143,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk544_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk545_0 (pattern : Twelve) : walkGuard ⟨163,183,.south⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk545_0 : WalkBound ⟨163,183,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk545_0]; exact allowed)
  have checked := c9776 pattern guarded
  change d116 pattern ≤ d813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk545_1 (pattern : Twelve) : walkGuard ⟨163,183,.south⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk545_1 : WalkBound ⟨163,183,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk545_1]; exact allowed)
  have checked := c9777 pattern guarded
  change d871 pattern ≤ d1274 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk545_2 (pattern : Twelve) : walkGuard ⟨163,183,.south⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk545_2 : WalkBound ⟨163,183,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk545_2]; exact allowed)
  have checked := c9778 pattern guarded
  change d1323 pattern ≤ d1643 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk545_3 (pattern : Twelve) : walkGuard ⟨163,183,.south⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk545_3 : WalkBound ⟨163,183,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk545_3]; exact allowed)
  have checked := c9779 pattern guarded
  change d1664 pattern ≤ d1834 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk546_0 (pattern : Twelve) : walkGuard ⟨163,162,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk546_0 : WalkBound ⟨163,162,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk546_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk546_1 (pattern : Twelve) : walkGuard ⟨163,162,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk546_1 : WalkBound ⟨163,162,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk546_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk546_2 (pattern : Twelve) : walkGuard ⟨163,162,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk546_2 : WalkBound ⟨163,162,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk546_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk546_3 (pattern : Twelve) : walkGuard ⟨163,162,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk546_3 : WalkBound ⟨163,162,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk546_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk547_0 (pattern : Twelve) : walkGuard ⟨163,184,.southEast⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk547_0 : WalkBound ⟨163,184,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk547_0]; exact allowed)
  have checked := c9781 pattern guarded
  change d116 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk547_1 (pattern : Twelve) : walkGuard ⟨163,184,.southEast⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk547_1 : WalkBound ⟨163,184,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk547_1]; exact allowed)
  have checked := c9783 pattern guarded
  change d871 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk547_2 (pattern : Twelve) : walkGuard ⟨163,184,.southEast⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk547_2 : WalkBound ⟨163,184,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk547_2]; exact allowed)
  have checked := c9785 pattern guarded
  change d1323 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk547_3 (pattern : Twelve) : walkGuard ⟨163,184,.southEast⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk547_3 : WalkBound ⟨163,184,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk547_3]; exact allowed)
  have checked := c9787 pattern guarded
  change d1664 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk548_0 (pattern : Twelve) : walkGuard ⟨163,182,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk548_0 : WalkBound ⟨163,182,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk548_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk548_1 (pattern : Twelve) : walkGuard ⟨163,182,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk548_1 : WalkBound ⟨163,182,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk548_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk548_2 (pattern : Twelve) : walkGuard ⟨163,182,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk548_2 : WalkBound ⟨163,182,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk548_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk548_3 (pattern : Twelve) : walkGuard ⟨163,182,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk548_3 : WalkBound ⟨163,182,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk548_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk549_0 (pattern : Twelve) : walkGuard ⟨163,142,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk549_0 : WalkBound ⟨163,142,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk549_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk549_1 (pattern : Twelve) : walkGuard ⟨163,142,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk549_1 : WalkBound ⟨163,142,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk549_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk549_2 (pattern : Twelve) : walkGuard ⟨163,142,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk549_2 : WalkBound ⟨163,142,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk549_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk549_3 (pattern : Twelve) : walkGuard ⟨163,142,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk549_3 : WalkBound ⟨163,142,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk549_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
