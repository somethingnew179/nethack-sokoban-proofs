/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers34
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk437_2 (pattern : Twelve) : walkGuard ⟨130,149,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk437_2 : WalkBound ⟨130,149,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk437_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk437_3 (pattern : Twelve) : walkGuard ⟨130,149,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk437_3 : WalkBound ⟨130,149,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk437_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk438_0 (pattern : Twelve) : walkGuard ⟨130,109,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk438_0 : WalkBound ⟨130,109,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk438_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk438_1 (pattern : Twelve) : walkGuard ⟨130,109,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk438_1 : WalkBound ⟨130,109,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk438_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk438_2 (pattern : Twelve) : walkGuard ⟨130,109,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk438_2 : WalkBound ⟨130,109,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk438_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk438_3 (pattern : Twelve) : walkGuard ⟨130,109,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk438_3 : WalkBound ⟨130,109,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk438_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk439_0 (pattern : Twelve) : walkGuard ⟨131,111,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk439_0 : WalkBound ⟨131,111,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk439_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk439_1 (pattern : Twelve) : walkGuard ⟨131,111,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk439_1 : WalkBound ⟨131,111,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk439_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk439_2 (pattern : Twelve) : walkGuard ⟨131,111,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk439_2 : WalkBound ⟨131,111,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk439_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk439_3 (pattern : Twelve) : walkGuard ⟨131,111,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk439_3 : WalkBound ⟨131,111,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk439_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk440_0 (pattern : Twelve) : walkGuard ⟨131,130,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk440_0 : WalkBound ⟨131,130,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk440_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk440_1 (pattern : Twelve) : walkGuard ⟨131,130,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk440_1 : WalkBound ⟨131,130,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk440_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk440_2 (pattern : Twelve) : walkGuard ⟨131,130,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk440_2 : WalkBound ⟨131,130,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk440_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk440_3 (pattern : Twelve) : walkGuard ⟨131,130,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk440_3 : WalkBound ⟨131,130,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk440_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk441_0 (pattern : Twelve) : walkGuard ⟨131,112,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk441_0 : WalkBound ⟨131,112,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk441_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk441_1 (pattern : Twelve) : walkGuard ⟨131,112,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk441_1 : WalkBound ⟨131,112,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk441_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk441_2 (pattern : Twelve) : walkGuard ⟨131,112,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk441_2 : WalkBound ⟨131,112,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk441_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk441_3 (pattern : Twelve) : walkGuard ⟨131,112,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk441_3 : WalkBound ⟨131,112,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk441_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk442_0 (pattern : Twelve) : walkGuard ⟨131,150,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk442_0 : WalkBound ⟨131,150,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk442_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk442_1 (pattern : Twelve) : walkGuard ⟨131,150,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk442_1 : WalkBound ⟨131,150,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk442_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk442_2 (pattern : Twelve) : walkGuard ⟨131,150,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk442_2 : WalkBound ⟨131,150,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk442_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk442_3 (pattern : Twelve) : walkGuard ⟨131,150,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk442_3 : WalkBound ⟨131,150,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk442_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk443_0 (pattern : Twelve) : walkGuard ⟨131,110,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk443_0 : WalkBound ⟨131,110,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk443_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk443_1 (pattern : Twelve) : walkGuard ⟨131,110,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk443_1 : WalkBound ⟨131,110,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk443_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk443_2 (pattern : Twelve) : walkGuard ⟨131,110,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk443_2 : WalkBound ⟨131,110,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk443_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk443_3 (pattern : Twelve) : walkGuard ⟨131,110,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk443_3 : WalkBound ⟨131,110,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk443_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk444_0 (pattern : Twelve) : walkGuard ⟨134,114,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk444_0 : WalkBound ⟨134,114,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk444_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk444_1 (pattern : Twelve) : walkGuard ⟨134,114,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk444_1 : WalkBound ⟨134,114,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk444_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk444_2 (pattern : Twelve) : walkGuard ⟨134,114,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk444_2 : WalkBound ⟨134,114,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk444_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk444_3 (pattern : Twelve) : walkGuard ⟨134,114,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk444_3 : WalkBound ⟨134,114,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk444_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk445_0 (pattern : Twelve) : walkGuard ⟨134,135,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk445_0 : WalkBound ⟨134,135,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk445_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk445_1 (pattern : Twelve) : walkGuard ⟨134,135,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk445_1 : WalkBound ⟨134,135,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk445_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk445_2 (pattern : Twelve) : walkGuard ⟨134,135,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk445_2 : WalkBound ⟨134,135,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk445_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk445_3 (pattern : Twelve) : walkGuard ⟨134,135,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk445_3 : WalkBound ⟨134,135,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk445_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk446_0 (pattern : Twelve) : walkGuard ⟨134,154,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk446_0 : WalkBound ⟨134,154,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk446_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk446_1 (pattern : Twelve) : walkGuard ⟨134,154,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk446_1 : WalkBound ⟨134,154,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk446_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk446_2 (pattern : Twelve) : walkGuard ⟨134,154,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk446_2 : WalkBound ⟨134,154,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk446_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk446_3 (pattern : Twelve) : walkGuard ⟨134,154,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk446_3 : WalkBound ⟨134,154,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk446_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk447_0 (pattern : Twelve) : walkGuard ⟨134,115,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk447_0 : WalkBound ⟨134,115,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk447_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk447_1 (pattern : Twelve) : walkGuard ⟨134,115,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk447_1 : WalkBound ⟨134,115,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk447_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk447_2 (pattern : Twelve) : walkGuard ⟨134,115,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk447_2 : WalkBound ⟨134,115,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk447_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk447_3 (pattern : Twelve) : walkGuard ⟨134,115,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk447_3 : WalkBound ⟨134,115,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk447_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk448_0 (pattern : Twelve) : walkGuard ⟨134,155,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk448_0 : WalkBound ⟨134,155,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk448_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk448_1 (pattern : Twelve) : walkGuard ⟨134,155,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk448_1 : WalkBound ⟨134,155,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk448_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk448_2 (pattern : Twelve) : walkGuard ⟨134,155,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk448_2 : WalkBound ⟨134,155,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk448_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk448_3 (pattern : Twelve) : walkGuard ⟨134,155,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk448_3 : WalkBound ⟨134,155,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk448_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk449_0 (pattern : Twelve) : walkGuard ⟨135,115,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk449_0 : WalkBound ⟨135,115,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk449_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk449_1 (pattern : Twelve) : walkGuard ⟨135,115,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk449_1 : WalkBound ⟨135,115,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk449_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk449_2 (pattern : Twelve) : walkGuard ⟨135,115,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk449_2 : WalkBound ⟨135,115,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk449_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk449_3 (pattern : Twelve) : walkGuard ⟨135,115,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk449_3 : WalkBound ⟨135,115,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk449_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
