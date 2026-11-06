/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers38
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk487_2 (pattern : Twelve) : walkGuard ⟨142,163,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk487_2 : WalkBound ⟨142,163,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk487_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk487_3 (pattern : Twelve) : walkGuard ⟨142,163,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk487_3 : WalkBound ⟨142,163,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk487_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk488_0 (pattern : Twelve) : walkGuard ⟨142,121,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk488_0 : WalkBound ⟨142,121,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk488_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk488_1 (pattern : Twelve) : walkGuard ⟨142,121,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk488_1 : WalkBound ⟨142,121,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk488_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk488_2 (pattern : Twelve) : walkGuard ⟨142,121,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk488_2 : WalkBound ⟨142,121,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk488_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk488_3 (pattern : Twelve) : walkGuard ⟨142,121,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk488_3 : WalkBound ⟨142,121,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk488_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk489_0 (pattern : Twelve) : walkGuard ⟨143,123,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk489_0 : WalkBound ⟨143,123,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk489_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk489_1 (pattern : Twelve) : walkGuard ⟨143,123,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk489_1 : WalkBound ⟨143,123,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk489_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk489_2 (pattern : Twelve) : walkGuard ⟨143,123,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk489_2 : WalkBound ⟨143,123,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk489_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk489_3 (pattern : Twelve) : walkGuard ⟨143,123,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk489_3 : WalkBound ⟨143,123,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk489_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk490_0 (pattern : Twelve) : walkGuard ⟨143,163,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk490_0 : WalkBound ⟨143,163,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk490_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk490_1 (pattern : Twelve) : walkGuard ⟨143,163,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk490_1 : WalkBound ⟨143,163,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk490_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk490_2 (pattern : Twelve) : walkGuard ⟨143,163,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk490_2 : WalkBound ⟨143,163,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk490_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk490_3 (pattern : Twelve) : walkGuard ⟨143,163,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk490_3 : WalkBound ⟨143,163,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk490_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk491_0 (pattern : Twelve) : walkGuard ⟨143,142,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk491_0 : WalkBound ⟨143,142,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk491_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk491_1 (pattern : Twelve) : walkGuard ⟨143,142,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk491_1 : WalkBound ⟨143,142,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk491_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk491_2 (pattern : Twelve) : walkGuard ⟨143,142,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk491_2 : WalkBound ⟨143,142,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk491_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk491_3 (pattern : Twelve) : walkGuard ⟨143,142,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk491_3 : WalkBound ⟨143,142,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk491_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk492_0 (pattern : Twelve) : walkGuard ⟨143,162,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk492_0 : WalkBound ⟨143,162,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk492_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk492_1 (pattern : Twelve) : walkGuard ⟨143,162,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk492_1 : WalkBound ⟨143,162,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk492_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk492_2 (pattern : Twelve) : walkGuard ⟨143,162,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk492_2 : WalkBound ⟨143,162,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk492_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk492_3 (pattern : Twelve) : walkGuard ⟨143,162,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk492_3 : WalkBound ⟨143,162,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk492_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk493_0 (pattern : Twelve) : walkGuard ⟨143,122,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk493_0 : WalkBound ⟨143,122,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk493_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk493_1 (pattern : Twelve) : walkGuard ⟨143,122,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk493_1 : WalkBound ⟨143,122,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk493_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk493_2 (pattern : Twelve) : walkGuard ⟨143,122,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk493_2 : WalkBound ⟨143,122,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk493_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk493_3 (pattern : Twelve) : walkGuard ⟨143,122,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk493_3 : WalkBound ⟨143,122,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk493_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk494_0 (pattern : Twelve) : walkGuard ⟨145,125,.north⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk494_0 : WalkBound ⟨145,125,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk494_0]; exact allowed)
  have checked := c9737 pattern guarded
  change d812 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk494_1 (pattern : Twelve) : walkGuard ⟨145,125,.north⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk494_1 : WalkBound ⟨145,125,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk494_1]; exact allowed)
  have checked := c9742 pattern guarded
  change d1273 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk494_2 (pattern : Twelve) : walkGuard ⟨145,125,.north⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk494_2 : WalkBound ⟨145,125,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk494_2]; exact allowed)
  have checked := c9747 pattern guarded
  change d1642 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk494_3 (pattern : Twelve) : walkGuard ⟨145,125,.north⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk494_3 : WalkBound ⟨145,125,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk494_3]; exact allowed)
  have checked := c9751 pattern guarded
  change d1833 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk495_0 (pattern : Twelve) : walkGuard ⟨145,146,.east⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk495_0 : WalkBound ⟨145,146,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk495_0]; exact allowed)
  have checked := c9737 pattern guarded
  change d812 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk495_1 (pattern : Twelve) : walkGuard ⟨145,146,.east⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk495_1 : WalkBound ⟨145,146,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk495_1]; exact allowed)
  have checked := c9742 pattern guarded
  change d1273 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk495_2 (pattern : Twelve) : walkGuard ⟨145,146,.east⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk495_2 : WalkBound ⟨145,146,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk495_2]; exact allowed)
  have checked := c9747 pattern guarded
  change d1642 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk495_3 (pattern : Twelve) : walkGuard ⟨145,146,.east⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk495_3 : WalkBound ⟨145,146,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk495_3]; exact allowed)
  have checked := c9751 pattern guarded
  change d1833 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk496_0 (pattern : Twelve) : walkGuard ⟨145,165,.south⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk496_0 : WalkBound ⟨145,165,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk496_0]; exact allowed)
  have checked := c9737 pattern guarded
  change d812 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk496_1 (pattern : Twelve) : walkGuard ⟨145,165,.south⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk496_1 : WalkBound ⟨145,165,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk496_1]; exact allowed)
  have checked := c9742 pattern guarded
  change d1273 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk496_2 (pattern : Twelve) : walkGuard ⟨145,165,.south⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk496_2 : WalkBound ⟨145,165,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk496_2]; exact allowed)
  have checked := c9747 pattern guarded
  change d1642 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk496_3 (pattern : Twelve) : walkGuard ⟨145,165,.south⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk496_3 : WalkBound ⟨145,165,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk496_3]; exact allowed)
  have checked := c9751 pattern guarded
  change d1833 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk497_0 (pattern : Twelve) : walkGuard ⟨145,126,.northEast⟩ 0 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk497_0 : WalkBound ⟨145,126,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk497_0]; exact allowed)
  have checked := c9756 pattern guarded
  change d812 pattern ≤ d809 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk497_1 (pattern : Twelve) : walkGuard ⟨145,126,.northEast⟩ 1 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk497_1 : WalkBound ⟨145,126,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk497_1]; exact allowed)
  have checked := c9761 pattern guarded
  change d1273 pattern ≤ d1270 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk497_2 (pattern : Twelve) : walkGuard ⟨145,126,.northEast⟩ 2 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk497_2 : WalkBound ⟨145,126,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk497_2]; exact allowed)
  have checked := c9766 pattern guarded
  change d1642 pattern ≤ d1639 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk497_3 (pattern : Twelve) : walkGuard ⟨145,126,.northEast⟩ 3 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk497_3 : WalkBound ⟨145,126,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk497_3]; exact allowed)
  have checked := c9771 pattern guarded
  change d1833 pattern ≤ d1830 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk498_0 (pattern : Twelve) : walkGuard ⟨145,166,.southEast⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk498_0 : WalkBound ⟨145,166,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk498_0]; exact allowed)
  have checked := c9737 pattern guarded
  change d812 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk498_1 (pattern : Twelve) : walkGuard ⟨145,166,.southEast⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk498_1 : WalkBound ⟨145,166,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk498_1]; exact allowed)
  have checked := c9742 pattern guarded
  change d1273 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk498_2 (pattern : Twelve) : walkGuard ⟨145,166,.southEast⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk498_2 : WalkBound ⟨145,166,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk498_2]; exact allowed)
  have checked := c9747 pattern guarded
  change d1642 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk498_3 (pattern : Twelve) : walkGuard ⟨145,166,.southEast⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk498_3 : WalkBound ⟨145,166,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk498_3]; exact allowed)
  have checked := c9751 pattern guarded
  change d1833 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk499_0 (pattern : Twelve) : walkGuard ⟨146,126,.north⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk499_0 : WalkBound ⟨146,126,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk499_0]; exact allowed)
  have checked := c9612 pattern guarded
  change d806 pattern ≤ d809 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk499_1 (pattern : Twelve) : walkGuard ⟨146,126,.north⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk499_1 : WalkBound ⟨146,126,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk499_1]; exact allowed)
  have checked := c9617 pattern guarded
  change d1267 pattern ≤ d1270 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk499_2 (pattern : Twelve) : walkGuard ⟨146,126,.north⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk499_2 : WalkBound ⟨146,126,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk499_2]; exact allowed)
  have checked := c9622 pattern guarded
  change d1636 pattern ≤ d1639 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk499_3 (pattern : Twelve) : walkGuard ⟨146,126,.north⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk499_3 : WalkBound ⟨146,126,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk499_3]; exact allowed)
  have checked := c9625 pattern guarded
  change d1827 pattern ≤ d1830 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
