/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers14
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk187_2 (pattern : Twelve) : walkGuard ⟨70,50,.north⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk187_2 : WalkBound ⟨70,50,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk187_2]; exact allowed)
  have checked := c7341 pattern guarded
  change d1556 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk187_3 (pattern : Twelve) : walkGuard ⟨70,50,.north⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk187_3 : WalkBound ⟨70,50,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk187_3]; exact allowed)
  have checked := c7378 pattern guarded
  change d1779 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk188_0 (pattern : Twelve) : walkGuard ⟨70,71,.east⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk188_0 : WalkBound ⟨70,71,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk188_0]; exact allowed)
  have checked := c7549 pattern guarded
  change d629 pattern ≤ d777 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk188_1 (pattern : Twelve) : walkGuard ⟨70,71,.east⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk188_1 : WalkBound ⟨70,71,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk188_1]; exact allowed)
  have checked := c7628 pattern guarded
  change d1182 pattern ≤ d1246 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk188_2 (pattern : Twelve) : walkGuard ⟨70,71,.east⟩ 2 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk188_2 : WalkBound ⟨70,71,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk188_2]; exact allowed)
  have checked := c7692 pattern guarded
  change d1556 pattern ≤ d1615 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk188_3 (pattern : Twelve) : walkGuard ⟨70,71,.east⟩ 3 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk188_3 : WalkBound ⟨70,71,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk188_3]; exact allowed)
  have checked := c7729 pattern guarded
  change d1779 pattern ≤ d1813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk189_0 (pattern : Twelve) : walkGuard ⟨70,90,.south⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk189_0 : WalkBound ⟨70,90,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk189_0]; exact allowed)
  have checked := c7179 pattern guarded
  change d629 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk189_1 (pattern : Twelve) : walkGuard ⟨70,90,.south⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk189_1 : WalkBound ⟨70,90,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk189_1]; exact allowed)
  have checked := c7271 pattern guarded
  change d1182 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk189_2 (pattern : Twelve) : walkGuard ⟨70,90,.south⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk189_2 : WalkBound ⟨70,90,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk189_2]; exact allowed)
  have checked := c7341 pattern guarded
  change d1556 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk189_3 (pattern : Twelve) : walkGuard ⟨70,90,.south⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk189_3 : WalkBound ⟨70,90,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk189_3]; exact allowed)
  have checked := c7378 pattern guarded
  change d1779 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk190_0 (pattern : Twelve) : walkGuard ⟨71,72,.east⟩ 0 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk190_0 : WalkBound ⟨71,72,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk190_0]; exact allowed)
  have checked := c7928 pattern guarded
  change d777 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk190_1 (pattern : Twelve) : walkGuard ⟨71,72,.east⟩ 1 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk190_1 : WalkBound ⟨71,72,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk190_1]; exact allowed)
  have checked := c8018 pattern guarded
  change d1246 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk190_2 (pattern : Twelve) : walkGuard ⟨71,72,.east⟩ 2 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk190_2 : WalkBound ⟨71,72,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk190_2]; exact allowed)
  have checked := c8087 pattern guarded
  change d1615 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk190_3 (pattern : Twelve) : walkGuard ⟨71,72,.east⟩ 3 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk190_3 : WalkBound ⟨71,72,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk190_3]; exact allowed)
  have checked := c8121 pattern guarded
  change d1813 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk191_0 (pattern : Twelve) : walkGuard ⟨71,70,.west⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk191_0 : WalkBound ⟨71,70,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk191_0]; exact allowed)
  have checked := c8290 pattern guarded
  change d777 pattern ≤ d629 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk191_1 (pattern : Twelve) : walkGuard ⟨71,70,.west⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk191_1 : WalkBound ⟨71,70,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk191_1]; exact allowed)
  have checked := c8369 pattern guarded
  change d1246 pattern ≤ d1182 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk191_2 (pattern : Twelve) : walkGuard ⟨71,70,.west⟩ 2 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk191_2 : WalkBound ⟨71,70,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk191_2]; exact allowed)
  have checked := c8433 pattern guarded
  change d1615 pattern ≤ d1556 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk191_3 (pattern : Twelve) : walkGuard ⟨71,70,.west⟩ 3 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk191_3 : WalkBound ⟨71,70,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk191_3]; exact allowed)
  have checked := c8470 pattern guarded
  change d1813 pattern ≤ d1779 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk192_0 (pattern : Twelve) : walkGuard ⟨71,52,.northEast⟩ 0 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk192_0 : WalkBound ⟨71,52,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk192_0]; exact allowed)
  have checked := c7928 pattern guarded
  change d777 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk192_1 (pattern : Twelve) : walkGuard ⟨71,52,.northEast⟩ 1 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk192_1 : WalkBound ⟨71,52,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk192_1]; exact allowed)
  have checked := c8018 pattern guarded
  change d1246 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk192_2 (pattern : Twelve) : walkGuard ⟨71,52,.northEast⟩ 2 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk192_2 : WalkBound ⟨71,52,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk192_2]; exact allowed)
  have checked := c8087 pattern guarded
  change d1615 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk192_3 (pattern : Twelve) : walkGuard ⟨71,52,.northEast⟩ 3 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk192_3 : WalkBound ⟨71,52,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk192_3]; exact allowed)
  have checked := c8121 pattern guarded
  change d1813 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk193_0 (pattern : Twelve) : walkGuard ⟨71,92,.southEast⟩ 0 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk193_0 : WalkBound ⟨71,92,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk193_0]; exact allowed)
  have checked := c7928 pattern guarded
  change d777 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk193_1 (pattern : Twelve) : walkGuard ⟨71,92,.southEast⟩ 1 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk193_1 : WalkBound ⟨71,92,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk193_1]; exact allowed)
  have checked := c8018 pattern guarded
  change d1246 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk193_2 (pattern : Twelve) : walkGuard ⟨71,92,.southEast⟩ 2 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk193_2 : WalkBound ⟨71,92,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk193_2]; exact allowed)
  have checked := c8087 pattern guarded
  change d1615 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk193_3 (pattern : Twelve) : walkGuard ⟨71,92,.southEast⟩ 3 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk193_3 : WalkBound ⟨71,92,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk193_3]; exact allowed)
  have checked := c8121 pattern guarded
  change d1813 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk194_0 (pattern : Twelve) : walkGuard ⟨71,90,.southWest⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk194_0 : WalkBound ⟨71,90,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk194_0]; exact allowed)
  have checked := c8662 pattern guarded
  change d777 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk194_1 (pattern : Twelve) : walkGuard ⟨71,90,.southWest⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk194_1 : WalkBound ⟨71,90,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk194_1]; exact allowed)
  have checked := c8753 pattern guarded
  change d1246 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk194_2 (pattern : Twelve) : walkGuard ⟨71,90,.southWest⟩ 2 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk194_2 : WalkBound ⟨71,90,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk194_2]; exact allowed)
  have checked := c8823 pattern guarded
  change d1615 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk194_3 (pattern : Twelve) : walkGuard ⟨71,90,.southWest⟩ 3 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk194_3 : WalkBound ⟨71,90,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk194_3]; exact allowed)
  have checked := c8857 pattern guarded
  change d1813 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk195_0 (pattern : Twelve) : walkGuard ⟨71,50,.northWest⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk195_0 : WalkBound ⟨71,50,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk195_0]; exact allowed)
  have checked := c8662 pattern guarded
  change d777 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk195_1 (pattern : Twelve) : walkGuard ⟨71,50,.northWest⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk195_1 : WalkBound ⟨71,50,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk195_1]; exact allowed)
  have checked := c8753 pattern guarded
  change d1246 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk195_2 (pattern : Twelve) : walkGuard ⟨71,50,.northWest⟩ 2 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk195_2 : WalkBound ⟨71,50,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk195_2]; exact allowed)
  have checked := c8823 pattern guarded
  change d1615 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk195_3 (pattern : Twelve) : walkGuard ⟨71,50,.northWest⟩ 3 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk195_3 : WalkBound ⟨71,50,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk195_3]; exact allowed)
  have checked := c8857 pattern guarded
  change d1813 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk196_0 (pattern : Twelve) : walkGuard ⟨72,52,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk196_0 : WalkBound ⟨72,52,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk196_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk196_1 (pattern : Twelve) : walkGuard ⟨72,52,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk196_1 : WalkBound ⟨72,52,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk196_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk196_2 (pattern : Twelve) : walkGuard ⟨72,52,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk196_2 : WalkBound ⟨72,52,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk196_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk196_3 (pattern : Twelve) : walkGuard ⟨72,52,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk196_3 : WalkBound ⟨72,52,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk196_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk197_0 (pattern : Twelve) : walkGuard ⟨72,92,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk197_0 : WalkBound ⟨72,92,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk197_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk197_1 (pattern : Twelve) : walkGuard ⟨72,92,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk197_1 : WalkBound ⟨72,92,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk197_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk197_2 (pattern : Twelve) : walkGuard ⟨72,92,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk197_2 : WalkBound ⟨72,92,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk197_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk197_3 (pattern : Twelve) : walkGuard ⟨72,92,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk197_3 : WalkBound ⟨72,92,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk197_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk198_0 (pattern : Twelve) : walkGuard ⟨72,71,.west⟩ 0 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk198_0 : WalkBound ⟨72,71,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk198_0]; exact allowed)
  have checked := c3847 pattern guarded
  change d156 pattern ≤ d777 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk198_1 (pattern : Twelve) : walkGuard ⟨72,71,.west⟩ 1 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk198_1 : WalkBound ⟨72,71,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk198_1]; exact allowed)
  have checked := c3938 pattern guarded
  change d907 pattern ≤ d1246 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk198_2 (pattern : Twelve) : walkGuard ⟨72,71,.west⟩ 2 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk198_2 : WalkBound ⟨72,71,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk198_2]; exact allowed)
  have checked := c4007 pattern guarded
  change d1354 pattern ≤ d1615 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk198_3 (pattern : Twelve) : walkGuard ⟨72,71,.west⟩ 3 pattern = decide (d1866 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases l <;> rfl
theorem walk198_3 : WalkBound ⟨72,71,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1866 pattern = 1 := of_decide_eq_true (by rw [← guard_walk198_3]; exact allowed)
  have checked := c4044 pattern guarded
  change d1678 pattern ≤ d1813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk199_0 (pattern : Twelve) : walkGuard ⟨74,54,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk199_0 : WalkBound ⟨74,54,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk199_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk199_1 (pattern : Twelve) : walkGuard ⟨74,54,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk199_1 : WalkBound ⟨74,54,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk199_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk199_2 (pattern : Twelve) : walkGuard ⟨74,54,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk199_2 : WalkBound ⟨74,54,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk199_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk199_3 (pattern : Twelve) : walkGuard ⟨74,54,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk199_3 : WalkBound ⟨74,54,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk199_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
