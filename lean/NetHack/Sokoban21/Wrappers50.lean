/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers49
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk625_0 (pattern : Twelve) : walkGuard ⟨202,182,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk625_0 : WalkBound ⟨202,182,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk625_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk625_1 (pattern : Twelve) : walkGuard ⟨202,182,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk625_1 : WalkBound ⟨202,182,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk625_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk625_2 (pattern : Twelve) : walkGuard ⟨202,182,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk625_2 : WalkBound ⟨202,182,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk625_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk625_3 (pattern : Twelve) : walkGuard ⟨202,182,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk625_3 : WalkBound ⟨202,182,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk625_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk626_0 (pattern : Twelve) : walkGuard ⟨202,203,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk626_0 : WalkBound ⟨202,203,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk626_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk626_1 (pattern : Twelve) : walkGuard ⟨202,203,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk626_1 : WalkBound ⟨202,203,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk626_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk626_2 (pattern : Twelve) : walkGuard ⟨202,203,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk626_2 : WalkBound ⟨202,203,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk626_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk626_3 (pattern : Twelve) : walkGuard ⟨202,203,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk626_3 : WalkBound ⟨202,203,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk626_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk627_0 (pattern : Twelve) : walkGuard ⟨202,201,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk627_0 : WalkBound ⟨202,201,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk627_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk627_1 (pattern : Twelve) : walkGuard ⟨202,201,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk627_1 : WalkBound ⟨202,201,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk627_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk627_2 (pattern : Twelve) : walkGuard ⟨202,201,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk627_2 : WalkBound ⟨202,201,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk627_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk627_3 (pattern : Twelve) : walkGuard ⟨202,201,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk627_3 : WalkBound ⟨202,201,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk627_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk628_0 (pattern : Twelve) : walkGuard ⟨202,183,.northEast⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk628_0 : WalkBound ⟨202,183,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk628_0]; exact allowed)
  have checked := c9776 pattern guarded
  change d116 pattern ≤ d813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk628_1 (pattern : Twelve) : walkGuard ⟨202,183,.northEast⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk628_1 : WalkBound ⟨202,183,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk628_1]; exact allowed)
  have checked := c9777 pattern guarded
  change d871 pattern ≤ d1274 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk628_2 (pattern : Twelve) : walkGuard ⟨202,183,.northEast⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk628_2 : WalkBound ⟨202,183,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk628_2]; exact allowed)
  have checked := c9778 pattern guarded
  change d1323 pattern ≤ d1643 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk628_3 (pattern : Twelve) : walkGuard ⟨202,183,.northEast⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk628_3 : WalkBound ⟨202,183,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk628_3]; exact allowed)
  have checked := c9779 pattern guarded
  change d1664 pattern ≤ d1834 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk629_0 (pattern : Twelve) : walkGuard ⟨202,181,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk629_0 : WalkBound ⟨202,181,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk629_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk629_1 (pattern : Twelve) : walkGuard ⟨202,181,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk629_1 : WalkBound ⟨202,181,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk629_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk629_2 (pattern : Twelve) : walkGuard ⟨202,181,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk629_2 : WalkBound ⟨202,181,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk629_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk629_3 (pattern : Twelve) : walkGuard ⟨202,181,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk629_3 : WalkBound ⟨202,181,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk629_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk630_0 (pattern : Twelve) : walkGuard ⟨203,183,.north⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk630_0 : WalkBound ⟨203,183,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk630_0]; exact allowed)
  have checked := c9776 pattern guarded
  change d116 pattern ≤ d813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk630_1 (pattern : Twelve) : walkGuard ⟨203,183,.north⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk630_1 : WalkBound ⟨203,183,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk630_1]; exact allowed)
  have checked := c9777 pattern guarded
  change d871 pattern ≤ d1274 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk630_2 (pattern : Twelve) : walkGuard ⟨203,183,.north⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk630_2 : WalkBound ⟨203,183,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk630_2]; exact allowed)
  have checked := c9778 pattern guarded
  change d1323 pattern ≤ d1643 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk630_3 (pattern : Twelve) : walkGuard ⟨203,183,.north⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk630_3 : WalkBound ⟨203,183,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk630_3]; exact allowed)
  have checked := c9779 pattern guarded
  change d1664 pattern ≤ d1834 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk631_0 (pattern : Twelve) : walkGuard ⟨203,202,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk631_0 : WalkBound ⟨203,202,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk631_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk631_1 (pattern : Twelve) : walkGuard ⟨203,202,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk631_1 : WalkBound ⟨203,202,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk631_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk631_2 (pattern : Twelve) : walkGuard ⟨203,202,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk631_2 : WalkBound ⟨203,202,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk631_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk631_3 (pattern : Twelve) : walkGuard ⟨203,202,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk631_3 : WalkBound ⟨203,202,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk631_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk632_0 (pattern : Twelve) : walkGuard ⟨203,184,.northEast⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk632_0 : WalkBound ⟨203,184,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk632_0]; exact allowed)
  have checked := c9781 pattern guarded
  change d116 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk632_1 (pattern : Twelve) : walkGuard ⟨203,184,.northEast⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk632_1 : WalkBound ⟨203,184,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk632_1]; exact allowed)
  have checked := c9783 pattern guarded
  change d871 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk632_2 (pattern : Twelve) : walkGuard ⟨203,184,.northEast⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk632_2 : WalkBound ⟨203,184,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk632_2]; exact allowed)
  have checked := c9785 pattern guarded
  change d1323 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk632_3 (pattern : Twelve) : walkGuard ⟨203,184,.northEast⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk632_3 : WalkBound ⟨203,184,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_walk632_3]; exact allowed)
  have checked := c9787 pattern guarded
  change d1664 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk633_0 (pattern : Twelve) : walkGuard ⟨203,182,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk633_0 : WalkBound ⟨203,182,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk633_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk633_1 (pattern : Twelve) : walkGuard ⟨203,182,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk633_1 : WalkBound ⟨203,182,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk633_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk633_2 (pattern : Twelve) : walkGuard ⟨203,182,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk633_2 : WalkBound ⟨203,182,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk633_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk633_3 (pattern : Twelve) : walkGuard ⟨203,182,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem walk633_3 : WalkBound ⟨203,182,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk633_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk634_0 (pattern : Twelve) : walkGuard ⟨205,185,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk634_0 : WalkBound ⟨205,185,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk634_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk634_1 (pattern : Twelve) : walkGuard ⟨205,185,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk634_1 : WalkBound ⟨205,185,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk634_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk634_2 (pattern : Twelve) : walkGuard ⟨205,185,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk634_2 : WalkBound ⟨205,185,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk634_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk634_3 (pattern : Twelve) : walkGuard ⟨205,185,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk634_3 : WalkBound ⟨205,185,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk634_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk635_0 (pattern : Twelve) : walkGuard ⟨205,206,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk635_0 : WalkBound ⟨205,206,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk635_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk635_1 (pattern : Twelve) : walkGuard ⟨205,206,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk635_1 : WalkBound ⟨205,206,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk635_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk635_2 (pattern : Twelve) : walkGuard ⟨205,206,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk635_2 : WalkBound ⟨205,206,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk635_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk635_3 (pattern : Twelve) : walkGuard ⟨205,206,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk635_3 : WalkBound ⟨205,206,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk635_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk636_0 (pattern : Twelve) : walkGuard ⟨205,186,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk636_0 : WalkBound ⟨205,186,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk636_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk636_1 (pattern : Twelve) : walkGuard ⟨205,186,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk636_1 : WalkBound ⟨205,186,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk636_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk636_2 (pattern : Twelve) : walkGuard ⟨205,186,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk636_2 : WalkBound ⟨205,186,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk636_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk636_3 (pattern : Twelve) : walkGuard ⟨205,186,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk636_3 : WalkBound ⟨205,186,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk636_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk637_0 (pattern : Twelve) : walkGuard ⟨205,184,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk637_0 : WalkBound ⟨205,184,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk637_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk637_1 (pattern : Twelve) : walkGuard ⟨205,184,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk637_1 : WalkBound ⟨205,184,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk637_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
