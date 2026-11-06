/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers45
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk575_0 (pattern : Twelve) : walkGuard ⟨183,203,.south⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk575_0 : WalkBound ⟨183,203,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk575_0]; exact allowed)
  have checked := c9788 pattern guarded
  change d813 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk575_1 (pattern : Twelve) : walkGuard ⟨183,203,.south⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk575_1 : WalkBound ⟨183,203,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk575_1]; exact allowed)
  have checked := c9789 pattern guarded
  change d1274 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk575_2 (pattern : Twelve) : walkGuard ⟨183,203,.south⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk575_2 : WalkBound ⟨183,203,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk575_2]; exact allowed)
  have checked := c9790 pattern guarded
  change d1643 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk575_3 (pattern : Twelve) : walkGuard ⟨183,203,.south⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk575_3 : WalkBound ⟨183,203,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk575_3]; exact allowed)
  have checked := c9791 pattern guarded
  change d1834 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk576_0 (pattern : Twelve) : walkGuard ⟨183,182,.west⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk576_0 : WalkBound ⟨183,182,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk576_0]; exact allowed)
  have checked := c9788 pattern guarded
  change d813 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk576_1 (pattern : Twelve) : walkGuard ⟨183,182,.west⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk576_1 : WalkBound ⟨183,182,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk576_1]; exact allowed)
  have checked := c9789 pattern guarded
  change d1274 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk576_2 (pattern : Twelve) : walkGuard ⟨183,182,.west⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk576_2 : WalkBound ⟨183,182,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk576_2]; exact allowed)
  have checked := c9790 pattern guarded
  change d1643 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk576_3 (pattern : Twelve) : walkGuard ⟨183,182,.west⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk576_3 : WalkBound ⟨183,182,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk576_3]; exact allowed)
  have checked := c9791 pattern guarded
  change d1834 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk577_0 (pattern : Twelve) : walkGuard ⟨183,202,.southWest⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk577_0 : WalkBound ⟨183,202,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk577_0]; exact allowed)
  have checked := c9788 pattern guarded
  change d813 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk577_1 (pattern : Twelve) : walkGuard ⟨183,202,.southWest⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk577_1 : WalkBound ⟨183,202,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk577_1]; exact allowed)
  have checked := c9789 pattern guarded
  change d1274 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk577_2 (pattern : Twelve) : walkGuard ⟨183,202,.southWest⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk577_2 : WalkBound ⟨183,202,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk577_2]; exact allowed)
  have checked := c9790 pattern guarded
  change d1643 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk577_3 (pattern : Twelve) : walkGuard ⟨183,202,.southWest⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk577_3 : WalkBound ⟨183,202,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk577_3]; exact allowed)
  have checked := c9791 pattern guarded
  change d1834 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk578_0 (pattern : Twelve) : walkGuard ⟨183,162,.northWest⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk578_0 : WalkBound ⟨183,162,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk578_0]; exact allowed)
  have checked := c9788 pattern guarded
  change d813 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk578_1 (pattern : Twelve) : walkGuard ⟨183,162,.northWest⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk578_1 : WalkBound ⟨183,162,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk578_1]; exact allowed)
  have checked := c9789 pattern guarded
  change d1274 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk578_2 (pattern : Twelve) : walkGuard ⟨183,162,.northWest⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk578_2 : WalkBound ⟨183,162,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk578_2]; exact allowed)
  have checked := c9790 pattern guarded
  change d1643 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk578_3 (pattern : Twelve) : walkGuard ⟨183,162,.northWest⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk578_3 : WalkBound ⟨183,162,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk578_3]; exact allowed)
  have checked := c9791 pattern guarded
  change d1834 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk579_0 (pattern : Twelve) : walkGuard ⟨184,185,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk579_0 : WalkBound ⟨184,185,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk579_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk579_1 (pattern : Twelve) : walkGuard ⟨184,185,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk579_1 : WalkBound ⟨184,185,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk579_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk579_2 (pattern : Twelve) : walkGuard ⟨184,185,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk579_2 : WalkBound ⟨184,185,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk579_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk579_3 (pattern : Twelve) : walkGuard ⟨184,185,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk579_3 : WalkBound ⟨184,185,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk579_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk580_0 (pattern : Twelve) : walkGuard ⟨184,183,.west⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk580_0 : WalkBound ⟨184,183,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk580_0]; exact allowed)
  have checked := c9796 pattern guarded
  change d806 pattern ≤ d813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk580_1 (pattern : Twelve) : walkGuard ⟨184,183,.west⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk580_1 : WalkBound ⟨184,183,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk580_1]; exact allowed)
  have checked := c9797 pattern guarded
  change d1267 pattern ≤ d1274 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk580_2 (pattern : Twelve) : walkGuard ⟨184,183,.west⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk580_2 : WalkBound ⟨184,183,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk580_2]; exact allowed)
  have checked := c9798 pattern guarded
  change d1636 pattern ≤ d1643 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk580_3 (pattern : Twelve) : walkGuard ⟨184,183,.west⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk580_3 : WalkBound ⟨184,183,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk580_3]; exact allowed)
  have checked := c9799 pattern guarded
  change d1827 pattern ≤ d1834 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk581_0 (pattern : Twelve) : walkGuard ⟨184,165,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk581_0 : WalkBound ⟨184,165,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk581_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk581_1 (pattern : Twelve) : walkGuard ⟨184,165,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk581_1 : WalkBound ⟨184,165,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk581_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk581_2 (pattern : Twelve) : walkGuard ⟨184,165,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk581_2 : WalkBound ⟨184,165,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk581_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk581_3 (pattern : Twelve) : walkGuard ⟨184,165,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk581_3 : WalkBound ⟨184,165,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk581_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk582_0 (pattern : Twelve) : walkGuard ⟨184,205,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk582_0 : WalkBound ⟨184,205,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk582_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk582_1 (pattern : Twelve) : walkGuard ⟨184,205,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk582_1 : WalkBound ⟨184,205,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk582_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk582_2 (pattern : Twelve) : walkGuard ⟨184,205,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk582_2 : WalkBound ⟨184,205,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk582_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk582_3 (pattern : Twelve) : walkGuard ⟨184,205,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk582_3 : WalkBound ⟨184,205,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk582_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk583_0 (pattern : Twelve) : walkGuard ⟨184,203,.southWest⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk583_0 : WalkBound ⟨184,203,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk583_0]; exact allowed)
  have checked := c9801 pattern guarded
  change d806 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk583_1 (pattern : Twelve) : walkGuard ⟨184,203,.southWest⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk583_1 : WalkBound ⟨184,203,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk583_1]; exact allowed)
  have checked := c9803 pattern guarded
  change d1267 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk583_2 (pattern : Twelve) : walkGuard ⟨184,203,.southWest⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk583_2 : WalkBound ⟨184,203,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk583_2]; exact allowed)
  have checked := c9805 pattern guarded
  change d1636 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk583_3 (pattern : Twelve) : walkGuard ⟨184,203,.southWest⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk583_3 : WalkBound ⟨184,203,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk583_3]; exact allowed)
  have checked := c9807 pattern guarded
  change d1827 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk584_0 (pattern : Twelve) : walkGuard ⟨184,163,.northWest⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk584_0 : WalkBound ⟨184,163,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk584_0]; exact allowed)
  have checked := c9801 pattern guarded
  change d806 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk584_1 (pattern : Twelve) : walkGuard ⟨184,163,.northWest⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk584_1 : WalkBound ⟨184,163,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk584_1]; exact allowed)
  have checked := c9803 pattern guarded
  change d1267 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk584_2 (pattern : Twelve) : walkGuard ⟨184,163,.northWest⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk584_2 : WalkBound ⟨184,163,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk584_2]; exact allowed)
  have checked := c9805 pattern guarded
  change d1636 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk584_3 (pattern : Twelve) : walkGuard ⟨184,163,.northWest⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk584_3 : WalkBound ⟨184,163,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk584_3]; exact allowed)
  have checked := c9807 pattern guarded
  change d1827 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk585_0 (pattern : Twelve) : walkGuard ⟨185,165,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk585_0 : WalkBound ⟨185,165,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk585_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk585_1 (pattern : Twelve) : walkGuard ⟨185,165,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk585_1 : WalkBound ⟨185,165,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk585_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk585_2 (pattern : Twelve) : walkGuard ⟨185,165,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk585_2 : WalkBound ⟨185,165,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk585_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk585_3 (pattern : Twelve) : walkGuard ⟨185,165,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk585_3 : WalkBound ⟨185,165,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk585_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk586_0 (pattern : Twelve) : walkGuard ⟨185,186,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk586_0 : WalkBound ⟨185,186,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk586_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk586_1 (pattern : Twelve) : walkGuard ⟨185,186,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk586_1 : WalkBound ⟨185,186,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk586_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk586_2 (pattern : Twelve) : walkGuard ⟨185,186,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk586_2 : WalkBound ⟨185,186,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk586_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk586_3 (pattern : Twelve) : walkGuard ⟨185,186,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk586_3 : WalkBound ⟨185,186,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk586_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk587_0 (pattern : Twelve) : walkGuard ⟨185,205,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk587_0 : WalkBound ⟨185,205,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk587_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk587_1 (pattern : Twelve) : walkGuard ⟨185,205,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk587_1 : WalkBound ⟨185,205,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk587_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
