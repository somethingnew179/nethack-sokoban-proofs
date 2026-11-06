/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers04
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk62_2 (pattern : Twelve) : walkGuard ⟨41,21,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk62_2 : WalkBound ⟨41,21,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk62_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk62_3 (pattern : Twelve) : walkGuard ⟨41,21,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk62_3 : WalkBound ⟨41,21,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk62_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_0 (pattern : Twelve) : walkGuard ⟨41,42,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk63_0 : WalkBound ⟨41,42,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_1 (pattern : Twelve) : walkGuard ⟨41,42,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk63_1 : WalkBound ⟨41,42,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_2 (pattern : Twelve) : walkGuard ⟨41,42,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk63_2 : WalkBound ⟨41,42,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_3 (pattern : Twelve) : walkGuard ⟨41,42,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk63_3 : WalkBound ⟨41,42,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_0 (pattern : Twelve) : walkGuard ⟨41,61,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk64_0 : WalkBound ⟨41,61,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_1 (pattern : Twelve) : walkGuard ⟨41,61,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk64_1 : WalkBound ⟨41,61,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_2 (pattern : Twelve) : walkGuard ⟨41,61,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk64_2 : WalkBound ⟨41,61,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_3 (pattern : Twelve) : walkGuard ⟨41,61,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk64_3 : WalkBound ⟨41,61,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_0 (pattern : Twelve) : walkGuard ⟨41,22,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk65_0 : WalkBound ⟨41,22,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_1 (pattern : Twelve) : walkGuard ⟨41,22,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk65_1 : WalkBound ⟨41,22,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_2 (pattern : Twelve) : walkGuard ⟨41,22,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk65_2 : WalkBound ⟨41,22,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_3 (pattern : Twelve) : walkGuard ⟨41,22,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk65_3 : WalkBound ⟨41,22,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_0 (pattern : Twelve) : walkGuard ⟨41,62,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk66_0 : WalkBound ⟨41,62,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_1 (pattern : Twelve) : walkGuard ⟨41,62,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk66_1 : WalkBound ⟨41,62,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_2 (pattern : Twelve) : walkGuard ⟨41,62,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk66_2 : WalkBound ⟨41,62,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_3 (pattern : Twelve) : walkGuard ⟨41,62,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk66_3 : WalkBound ⟨41,62,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_0 (pattern : Twelve) : walkGuard ⟨42,22,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk67_0 : WalkBound ⟨42,22,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_1 (pattern : Twelve) : walkGuard ⟨42,22,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk67_1 : WalkBound ⟨42,22,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_2 (pattern : Twelve) : walkGuard ⟨42,22,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk67_2 : WalkBound ⟨42,22,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_3 (pattern : Twelve) : walkGuard ⟨42,22,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk67_3 : WalkBound ⟨42,22,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_0 (pattern : Twelve) : walkGuard ⟨42,43,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk68_0 : WalkBound ⟨42,43,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_1 (pattern : Twelve) : walkGuard ⟨42,43,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk68_1 : WalkBound ⟨42,43,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_2 (pattern : Twelve) : walkGuard ⟨42,43,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk68_2 : WalkBound ⟨42,43,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_3 (pattern : Twelve) : walkGuard ⟨42,43,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk68_3 : WalkBound ⟨42,43,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_0 (pattern : Twelve) : walkGuard ⟨42,62,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk69_0 : WalkBound ⟨42,62,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_1 (pattern : Twelve) : walkGuard ⟨42,62,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk69_1 : WalkBound ⟨42,62,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_2 (pattern : Twelve) : walkGuard ⟨42,62,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk69_2 : WalkBound ⟨42,62,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_3 (pattern : Twelve) : walkGuard ⟨42,62,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk69_3 : WalkBound ⟨42,62,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk70_0 (pattern : Twelve) : walkGuard ⟨42,41,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk70_0 : WalkBound ⟨42,41,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk70_1 (pattern : Twelve) : walkGuard ⟨42,41,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk70_1 : WalkBound ⟨42,41,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk70_2 (pattern : Twelve) : walkGuard ⟨42,41,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk70_2 : WalkBound ⟨42,41,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk70_3 (pattern : Twelve) : walkGuard ⟨42,41,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk70_3 : WalkBound ⟨42,41,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_0 (pattern : Twelve) : walkGuard ⟨42,23,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk71_0 : WalkBound ⟨42,23,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_1 (pattern : Twelve) : walkGuard ⟨42,23,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk71_1 : WalkBound ⟨42,23,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_2 (pattern : Twelve) : walkGuard ⟨42,23,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk71_2 : WalkBound ⟨42,23,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_3 (pattern : Twelve) : walkGuard ⟨42,23,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk71_3 : WalkBound ⟨42,23,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_0 (pattern : Twelve) : walkGuard ⟨42,61,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk72_0 : WalkBound ⟨42,61,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_1 (pattern : Twelve) : walkGuard ⟨42,61,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk72_1 : WalkBound ⟨42,61,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_2 (pattern : Twelve) : walkGuard ⟨42,61,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk72_2 : WalkBound ⟨42,61,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_3 (pattern : Twelve) : walkGuard ⟨42,61,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk72_3 : WalkBound ⟨42,61,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_0 (pattern : Twelve) : walkGuard ⟨42,21,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk73_0 : WalkBound ⟨42,21,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_1 (pattern : Twelve) : walkGuard ⟨42,21,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk73_1 : WalkBound ⟨42,21,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_2 (pattern : Twelve) : walkGuard ⟨42,21,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk73_2 : WalkBound ⟨42,21,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_3 (pattern : Twelve) : walkGuard ⟨42,21,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk73_3 : WalkBound ⟨42,21,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_0 (pattern : Twelve) : walkGuard ⟨43,23,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk74_0 : WalkBound ⟨43,23,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_1 (pattern : Twelve) : walkGuard ⟨43,23,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk74_1 : WalkBound ⟨43,23,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_2 (pattern : Twelve) : walkGuard ⟨43,23,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk74_2 : WalkBound ⟨43,23,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_3 (pattern : Twelve) : walkGuard ⟨43,23,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk74_3 : WalkBound ⟨43,23,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
