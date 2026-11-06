/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers24
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk312_2 (pattern : Twelve) : walkGuard ⟨102,121,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk312_2 : WalkBound ⟨102,121,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk312_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk312_3 (pattern : Twelve) : walkGuard ⟨102,121,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk312_3 : WalkBound ⟨102,121,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk312_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk313_0 (pattern : Twelve) : walkGuard ⟨103,123,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk313_0 : WalkBound ⟨103,123,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk313_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk313_1 (pattern : Twelve) : walkGuard ⟨103,123,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk313_1 : WalkBound ⟨103,123,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk313_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk313_2 (pattern : Twelve) : walkGuard ⟨103,123,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk313_2 : WalkBound ⟨103,123,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk313_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk313_3 (pattern : Twelve) : walkGuard ⟨103,123,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk313_3 : WalkBound ⟨103,123,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk313_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk314_0 (pattern : Twelve) : walkGuard ⟨103,102,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk314_0 : WalkBound ⟨103,102,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk314_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk314_1 (pattern : Twelve) : walkGuard ⟨103,102,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk314_1 : WalkBound ⟨103,102,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk314_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk314_2 (pattern : Twelve) : walkGuard ⟨103,102,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk314_2 : WalkBound ⟨103,102,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk314_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk314_3 (pattern : Twelve) : walkGuard ⟨103,102,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk314_3 : WalkBound ⟨103,102,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk314_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk315_0 (pattern : Twelve) : walkGuard ⟨103,84,.northEast⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk315_0 : WalkBound ⟨103,84,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_0]; exact allowed)
  have checked := c8858 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk315_1 (pattern : Twelve) : walkGuard ⟨103,84,.northEast⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk315_1 : WalkBound ⟨103,84,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_1]; exact allowed)
  have checked := c8859 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk315_2 (pattern : Twelve) : walkGuard ⟨103,84,.northEast⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk315_2 : WalkBound ⟨103,84,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_2]; exact allowed)
  have checked := c8860 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk315_3 (pattern : Twelve) : walkGuard ⟨103,84,.northEast⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk315_3 : WalkBound ⟨103,84,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_3]; exact allowed)
  have checked := c8861 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_0 (pattern : Twelve) : walkGuard ⟨103,122,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk316_0 : WalkBound ⟨103,122,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_1 (pattern : Twelve) : walkGuard ⟨103,122,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk316_1 : WalkBound ⟨103,122,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_2 (pattern : Twelve) : walkGuard ⟨103,122,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk316_2 : WalkBound ⟨103,122,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_3 (pattern : Twelve) : walkGuard ⟨103,122,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk316_3 : WalkBound ⟨103,122,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_0 (pattern : Twelve) : walkGuard ⟨103,82,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk317_0 : WalkBound ⟨103,82,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_1 (pattern : Twelve) : walkGuard ⟨103,82,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk317_1 : WalkBound ⟨103,82,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_2 (pattern : Twelve) : walkGuard ⟨103,82,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk317_2 : WalkBound ⟨103,82,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_3 (pattern : Twelve) : walkGuard ⟨103,82,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk317_3 : WalkBound ⟨103,82,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_0 (pattern : Twelve) : walkGuard ⟨106,107,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk318_0 : WalkBound ⟨106,107,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_1 (pattern : Twelve) : walkGuard ⟨106,107,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk318_1 : WalkBound ⟨106,107,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_2 (pattern : Twelve) : walkGuard ⟨106,107,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk318_2 : WalkBound ⟨106,107,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_3 (pattern : Twelve) : walkGuard ⟨106,107,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk318_3 : WalkBound ⟨106,107,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_0 (pattern : Twelve) : walkGuard ⟨106,126,.south⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk319_0 : WalkBound ⟨106,126,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_0]; exact allowed)
  have checked := c9564 pattern guarded
  change d156 pattern ≤ d809 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_1 (pattern : Twelve) : walkGuard ⟨106,126,.south⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk319_1 : WalkBound ⟨106,126,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_1]; exact allowed)
  have checked := c9571 pattern guarded
  change d907 pattern ≤ d1270 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_2 (pattern : Twelve) : walkGuard ⟨106,126,.south⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk319_2 : WalkBound ⟨106,126,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_2]; exact allowed)
  have checked := c9578 pattern guarded
  change d1354 pattern ≤ d1639 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_3 (pattern : Twelve) : walkGuard ⟨106,126,.south⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk319_3 : WalkBound ⟨106,126,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_3]; exact allowed)
  have checked := c9584 pattern guarded
  change d1678 pattern ≤ d1830 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_0 (pattern : Twelve) : walkGuard ⟨106,87,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk320_0 : WalkBound ⟨106,87,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_1 (pattern : Twelve) : walkGuard ⟨106,87,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk320_1 : WalkBound ⟨106,87,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_2 (pattern : Twelve) : walkGuard ⟨106,87,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk320_2 : WalkBound ⟨106,87,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_3 (pattern : Twelve) : walkGuard ⟨106,87,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk320_3 : WalkBound ⟨106,87,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_0 (pattern : Twelve) : walkGuard ⟨106,127,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk321_0 : WalkBound ⟨106,127,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_1 (pattern : Twelve) : walkGuard ⟨106,127,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk321_1 : WalkBound ⟨106,127,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_2 (pattern : Twelve) : walkGuard ⟨106,127,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk321_2 : WalkBound ⟨106,127,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_3 (pattern : Twelve) : walkGuard ⟨106,127,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk321_3 : WalkBound ⟨106,127,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_0 (pattern : Twelve) : walkGuard ⟨106,125,.southWest⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk322_0 : WalkBound ⟨106,125,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_0]; exact allowed)
  have checked := c9589 pattern guarded
  change d156 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_1 (pattern : Twelve) : walkGuard ⟨106,125,.southWest⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk322_1 : WalkBound ⟨106,125,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_1]; exact allowed)
  have checked := c9594 pattern guarded
  change d907 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_2 (pattern : Twelve) : walkGuard ⟨106,125,.southWest⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk322_2 : WalkBound ⟨106,125,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_2]; exact allowed)
  have checked := c9599 pattern guarded
  change d1354 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_3 (pattern : Twelve) : walkGuard ⟨106,125,.southWest⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk322_3 : WalkBound ⟨106,125,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_3]; exact allowed)
  have checked := c9603 pattern guarded
  change d1678 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_0 (pattern : Twelve) : walkGuard ⟨106,85,.northWest⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk323_0 : WalkBound ⟨106,85,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_0]; exact allowed)
  have checked := c9604 pattern guarded
  change d156 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_1 (pattern : Twelve) : walkGuard ⟨106,85,.northWest⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk323_1 : WalkBound ⟨106,85,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_1]; exact allowed)
  have checked := c9605 pattern guarded
  change d907 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_2 (pattern : Twelve) : walkGuard ⟨106,85,.northWest⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk323_2 : WalkBound ⟨106,85,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_2]; exact allowed)
  have checked := c9606 pattern guarded
  change d1354 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_3 (pattern : Twelve) : walkGuard ⟨106,85,.northWest⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk323_3 : WalkBound ⟨106,85,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_3]; exact allowed)
  have checked := c9607 pattern guarded
  change d1678 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_0 (pattern : Twelve) : walkGuard ⟨107,87,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk324_0 : WalkBound ⟨107,87,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_1 (pattern : Twelve) : walkGuard ⟨107,87,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk324_1 : WalkBound ⟨107,87,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_2 (pattern : Twelve) : walkGuard ⟨107,87,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk324_2 : WalkBound ⟨107,87,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_3 (pattern : Twelve) : walkGuard ⟨107,87,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk324_3 : WalkBound ⟨107,87,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
