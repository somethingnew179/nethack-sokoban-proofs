/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers33
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk425_0 (pattern : Twelve) : walkGuard ⟨129,109,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk425_0 : WalkBound ⟨129,109,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk425_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk425_1 (pattern : Twelve) : walkGuard ⟨129,109,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk425_1 : WalkBound ⟨129,109,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk425_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk425_2 (pattern : Twelve) : walkGuard ⟨129,109,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk425_2 : WalkBound ⟨129,109,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk425_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk425_3 (pattern : Twelve) : walkGuard ⟨129,109,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk425_3 : WalkBound ⟨129,109,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk425_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk426_0 (pattern : Twelve) : walkGuard ⟨129,130,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk426_0 : WalkBound ⟨129,130,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk426_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk426_1 (pattern : Twelve) : walkGuard ⟨129,130,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk426_1 : WalkBound ⟨129,130,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk426_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk426_2 (pattern : Twelve) : walkGuard ⟨129,130,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk426_2 : WalkBound ⟨129,130,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk426_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk426_3 (pattern : Twelve) : walkGuard ⟨129,130,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk426_3 : WalkBound ⟨129,130,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk426_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk427_0 (pattern : Twelve) : walkGuard ⟨129,149,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk427_0 : WalkBound ⟨129,149,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk427_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk427_1 (pattern : Twelve) : walkGuard ⟨129,149,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk427_1 : WalkBound ⟨129,149,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk427_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk427_2 (pattern : Twelve) : walkGuard ⟨129,149,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk427_2 : WalkBound ⟨129,149,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk427_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk427_3 (pattern : Twelve) : walkGuard ⟨129,149,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk427_3 : WalkBound ⟨129,149,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk427_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk428_0 (pattern : Twelve) : walkGuard ⟨129,110,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk428_0 : WalkBound ⟨129,110,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk428_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk428_1 (pattern : Twelve) : walkGuard ⟨129,110,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk428_1 : WalkBound ⟨129,110,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk428_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk428_2 (pattern : Twelve) : walkGuard ⟨129,110,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk428_2 : WalkBound ⟨129,110,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk428_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk428_3 (pattern : Twelve) : walkGuard ⟨129,110,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk428_3 : WalkBound ⟨129,110,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk428_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk429_0 (pattern : Twelve) : walkGuard ⟨129,150,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk429_0 : WalkBound ⟨129,150,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk429_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk429_1 (pattern : Twelve) : walkGuard ⟨129,150,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk429_1 : WalkBound ⟨129,150,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk429_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk429_2 (pattern : Twelve) : walkGuard ⟨129,150,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk429_2 : WalkBound ⟨129,150,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk429_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk429_3 (pattern : Twelve) : walkGuard ⟨129,150,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk429_3 : WalkBound ⟨129,150,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk429_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk430_0 (pattern : Twelve) : walkGuard ⟨129,148,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk430_0 : WalkBound ⟨129,148,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk430_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk430_1 (pattern : Twelve) : walkGuard ⟨129,148,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk430_1 : WalkBound ⟨129,148,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk430_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk430_2 (pattern : Twelve) : walkGuard ⟨129,148,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk430_2 : WalkBound ⟨129,148,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk430_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk430_3 (pattern : Twelve) : walkGuard ⟨129,148,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk430_3 : WalkBound ⟨129,148,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk430_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk431_0 (pattern : Twelve) : walkGuard ⟨129,108,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk431_0 : WalkBound ⟨129,108,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk431_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk431_1 (pattern : Twelve) : walkGuard ⟨129,108,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk431_1 : WalkBound ⟨129,108,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk431_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk431_2 (pattern : Twelve) : walkGuard ⟨129,108,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk431_2 : WalkBound ⟨129,108,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk431_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk431_3 (pattern : Twelve) : walkGuard ⟨129,108,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk431_3 : WalkBound ⟨129,108,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk431_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk432_0 (pattern : Twelve) : walkGuard ⟨130,110,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk432_0 : WalkBound ⟨130,110,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk432_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk432_1 (pattern : Twelve) : walkGuard ⟨130,110,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk432_1 : WalkBound ⟨130,110,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk432_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk432_2 (pattern : Twelve) : walkGuard ⟨130,110,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk432_2 : WalkBound ⟨130,110,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk432_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk432_3 (pattern : Twelve) : walkGuard ⟨130,110,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk432_3 : WalkBound ⟨130,110,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk432_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk433_0 (pattern : Twelve) : walkGuard ⟨130,131,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk433_0 : WalkBound ⟨130,131,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk433_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk433_1 (pattern : Twelve) : walkGuard ⟨130,131,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk433_1 : WalkBound ⟨130,131,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk433_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk433_2 (pattern : Twelve) : walkGuard ⟨130,131,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk433_2 : WalkBound ⟨130,131,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk433_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk433_3 (pattern : Twelve) : walkGuard ⟨130,131,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk433_3 : WalkBound ⟨130,131,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk433_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk434_0 (pattern : Twelve) : walkGuard ⟨130,150,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk434_0 : WalkBound ⟨130,150,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk434_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk434_1 (pattern : Twelve) : walkGuard ⟨130,150,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk434_1 : WalkBound ⟨130,150,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk434_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk434_2 (pattern : Twelve) : walkGuard ⟨130,150,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk434_2 : WalkBound ⟨130,150,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk434_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk434_3 (pattern : Twelve) : walkGuard ⟨130,150,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk434_3 : WalkBound ⟨130,150,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk434_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk435_0 (pattern : Twelve) : walkGuard ⟨130,129,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk435_0 : WalkBound ⟨130,129,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk435_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk435_1 (pattern : Twelve) : walkGuard ⟨130,129,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk435_1 : WalkBound ⟨130,129,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk435_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk435_2 (pattern : Twelve) : walkGuard ⟨130,129,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk435_2 : WalkBound ⟨130,129,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk435_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk435_3 (pattern : Twelve) : walkGuard ⟨130,129,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk435_3 : WalkBound ⟨130,129,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk435_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk436_0 (pattern : Twelve) : walkGuard ⟨130,111,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk436_0 : WalkBound ⟨130,111,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk436_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk436_1 (pattern : Twelve) : walkGuard ⟨130,111,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk436_1 : WalkBound ⟨130,111,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk436_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk436_2 (pattern : Twelve) : walkGuard ⟨130,111,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk436_2 : WalkBound ⟨130,111,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk436_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk436_3 (pattern : Twelve) : walkGuard ⟨130,111,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk436_3 : WalkBound ⟨130,111,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk436_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk437_0 (pattern : Twelve) : walkGuard ⟨130,149,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk437_0 : WalkBound ⟨130,149,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk437_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk437_1 (pattern : Twelve) : walkGuard ⟨130,149,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk437_1 : WalkBound ⟨130,149,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk437_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
