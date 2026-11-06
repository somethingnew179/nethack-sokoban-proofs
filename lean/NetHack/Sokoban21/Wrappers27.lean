/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers26
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk337_2 (pattern : Twelve) : walkGuard ⟨109,129,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk337_2 : WalkBound ⟨109,129,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk337_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk337_3 (pattern : Twelve) : walkGuard ⟨109,129,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk337_3 : WalkBound ⟨109,129,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk337_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_0 (pattern : Twelve) : walkGuard ⟨109,108,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk338_0 : WalkBound ⟨109,108,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_1 (pattern : Twelve) : walkGuard ⟨109,108,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk338_1 : WalkBound ⟨109,108,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_2 (pattern : Twelve) : walkGuard ⟨109,108,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk338_2 : WalkBound ⟨109,108,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_3 (pattern : Twelve) : walkGuard ⟨109,108,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk338_3 : WalkBound ⟨109,108,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_0 (pattern : Twelve) : walkGuard ⟨109,90,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk339_0 : WalkBound ⟨109,90,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_1 (pattern : Twelve) : walkGuard ⟨109,90,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk339_1 : WalkBound ⟨109,90,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_2 (pattern : Twelve) : walkGuard ⟨109,90,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk339_2 : WalkBound ⟨109,90,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_3 (pattern : Twelve) : walkGuard ⟨109,90,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk339_3 : WalkBound ⟨109,90,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_0 (pattern : Twelve) : walkGuard ⟨109,130,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk340_0 : WalkBound ⟨109,130,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_1 (pattern : Twelve) : walkGuard ⟨109,130,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk340_1 : WalkBound ⟨109,130,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_2 (pattern : Twelve) : walkGuard ⟨109,130,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk340_2 : WalkBound ⟨109,130,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_3 (pattern : Twelve) : walkGuard ⟨109,130,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk340_3 : WalkBound ⟨109,130,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_0 (pattern : Twelve) : walkGuard ⟨109,88,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk341_0 : WalkBound ⟨109,88,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_1 (pattern : Twelve) : walkGuard ⟨109,88,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk341_1 : WalkBound ⟨109,88,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_2 (pattern : Twelve) : walkGuard ⟨109,88,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk341_2 : WalkBound ⟨109,88,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_3 (pattern : Twelve) : walkGuard ⟨109,88,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk341_3 : WalkBound ⟨109,88,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_0 (pattern : Twelve) : walkGuard ⟨110,90,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk342_0 : WalkBound ⟨110,90,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_1 (pattern : Twelve) : walkGuard ⟨110,90,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk342_1 : WalkBound ⟨110,90,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_2 (pattern : Twelve) : walkGuard ⟨110,90,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk342_2 : WalkBound ⟨110,90,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_3 (pattern : Twelve) : walkGuard ⟨110,90,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk342_3 : WalkBound ⟨110,90,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_0 (pattern : Twelve) : walkGuard ⟨110,111,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk343_0 : WalkBound ⟨110,111,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_1 (pattern : Twelve) : walkGuard ⟨110,111,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk343_1 : WalkBound ⟨110,111,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_2 (pattern : Twelve) : walkGuard ⟨110,111,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk343_2 : WalkBound ⟨110,111,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_3 (pattern : Twelve) : walkGuard ⟨110,111,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk343_3 : WalkBound ⟨110,111,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_0 (pattern : Twelve) : walkGuard ⟨110,130,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk344_0 : WalkBound ⟨110,130,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_1 (pattern : Twelve) : walkGuard ⟨110,130,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk344_1 : WalkBound ⟨110,130,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_2 (pattern : Twelve) : walkGuard ⟨110,130,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk344_2 : WalkBound ⟨110,130,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_3 (pattern : Twelve) : walkGuard ⟨110,130,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk344_3 : WalkBound ⟨110,130,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_0 (pattern : Twelve) : walkGuard ⟨110,109,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk345_0 : WalkBound ⟨110,109,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_1 (pattern : Twelve) : walkGuard ⟨110,109,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk345_1 : WalkBound ⟨110,109,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_2 (pattern : Twelve) : walkGuard ⟨110,109,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk345_2 : WalkBound ⟨110,109,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_3 (pattern : Twelve) : walkGuard ⟨110,109,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk345_3 : WalkBound ⟨110,109,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_0 (pattern : Twelve) : walkGuard ⟨110,131,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk346_0 : WalkBound ⟨110,131,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_1 (pattern : Twelve) : walkGuard ⟨110,131,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk346_1 : WalkBound ⟨110,131,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_2 (pattern : Twelve) : walkGuard ⟨110,131,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk346_2 : WalkBound ⟨110,131,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_3 (pattern : Twelve) : walkGuard ⟨110,131,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk346_3 : WalkBound ⟨110,131,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_0 (pattern : Twelve) : walkGuard ⟨110,129,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk347_0 : WalkBound ⟨110,129,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_1 (pattern : Twelve) : walkGuard ⟨110,129,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk347_1 : WalkBound ⟨110,129,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_2 (pattern : Twelve) : walkGuard ⟨110,129,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk347_2 : WalkBound ⟨110,129,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_3 (pattern : Twelve) : walkGuard ⟨110,129,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk347_3 : WalkBound ⟨110,129,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_0 (pattern : Twelve) : walkGuard ⟨111,112,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk348_0 : WalkBound ⟨111,112,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_1 (pattern : Twelve) : walkGuard ⟨111,112,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk348_1 : WalkBound ⟨111,112,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_2 (pattern : Twelve) : walkGuard ⟨111,112,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk348_2 : WalkBound ⟨111,112,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_3 (pattern : Twelve) : walkGuard ⟨111,112,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk348_3 : WalkBound ⟨111,112,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_0 (pattern : Twelve) : walkGuard ⟨111,131,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk349_0 : WalkBound ⟨111,131,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_1 (pattern : Twelve) : walkGuard ⟨111,131,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk349_1 : WalkBound ⟨111,131,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_2 (pattern : Twelve) : walkGuard ⟨111,131,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk349_2 : WalkBound ⟨111,131,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_3 (pattern : Twelve) : walkGuard ⟨111,131,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk349_3 : WalkBound ⟨111,131,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
