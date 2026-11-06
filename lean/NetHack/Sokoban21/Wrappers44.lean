/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers43
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk550_0 (pattern : Twelve) : walkGuard ⟨165,145,.north⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk550_0 : WalkBound ⟨165,145,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk550_0]; exact allowed)
  have checked := c9631 pattern guarded
  change d806 pattern ≤ d812 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk550_1 (pattern : Twelve) : walkGuard ⟨165,145,.north⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk550_1 : WalkBound ⟨165,145,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk550_1]; exact allowed)
  have checked := c9637 pattern guarded
  change d1267 pattern ≤ d1273 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk550_2 (pattern : Twelve) : walkGuard ⟨165,145,.north⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk550_2 : WalkBound ⟨165,145,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk550_2]; exact allowed)
  have checked := c9643 pattern guarded
  change d1636 pattern ≤ d1642 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk550_3 (pattern : Twelve) : walkGuard ⟨165,145,.north⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk550_3 : WalkBound ⟨165,145,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk550_3]; exact allowed)
  have checked := c9648 pattern guarded
  change d1827 pattern ≤ d1833 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk551_0 (pattern : Twelve) : walkGuard ⟨165,166,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk551_0 : WalkBound ⟨165,166,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk551_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk551_1 (pattern : Twelve) : walkGuard ⟨165,166,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk551_1 : WalkBound ⟨165,166,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk551_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk551_2 (pattern : Twelve) : walkGuard ⟨165,166,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk551_2 : WalkBound ⟨165,166,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk551_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk551_3 (pattern : Twelve) : walkGuard ⟨165,166,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk551_3 : WalkBound ⟨165,166,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk551_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk552_0 (pattern : Twelve) : walkGuard ⟨165,185,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk552_0 : WalkBound ⟨165,185,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk552_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk552_1 (pattern : Twelve) : walkGuard ⟨165,185,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk552_1 : WalkBound ⟨165,185,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk552_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk552_2 (pattern : Twelve) : walkGuard ⟨165,185,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk552_2 : WalkBound ⟨165,185,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk552_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk552_3 (pattern : Twelve) : walkGuard ⟨165,185,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk552_3 : WalkBound ⟨165,185,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk552_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk553_0 (pattern : Twelve) : walkGuard ⟨165,146,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk553_0 : WalkBound ⟨165,146,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk553_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk553_1 (pattern : Twelve) : walkGuard ⟨165,146,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk553_1 : WalkBound ⟨165,146,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk553_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk553_2 (pattern : Twelve) : walkGuard ⟨165,146,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk553_2 : WalkBound ⟨165,146,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk553_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk553_3 (pattern : Twelve) : walkGuard ⟨165,146,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk553_3 : WalkBound ⟨165,146,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk553_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk554_0 (pattern : Twelve) : walkGuard ⟨165,186,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk554_0 : WalkBound ⟨165,186,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk554_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk554_1 (pattern : Twelve) : walkGuard ⟨165,186,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk554_1 : WalkBound ⟨165,186,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk554_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk554_2 (pattern : Twelve) : walkGuard ⟨165,186,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk554_2 : WalkBound ⟨165,186,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk554_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk554_3 (pattern : Twelve) : walkGuard ⟨165,186,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk554_3 : WalkBound ⟨165,186,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk554_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk555_0 (pattern : Twelve) : walkGuard ⟨165,184,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk555_0 : WalkBound ⟨165,184,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk555_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk555_1 (pattern : Twelve) : walkGuard ⟨165,184,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk555_1 : WalkBound ⟨165,184,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk555_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk555_2 (pattern : Twelve) : walkGuard ⟨165,184,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk555_2 : WalkBound ⟨165,184,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk555_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk555_3 (pattern : Twelve) : walkGuard ⟨165,184,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk555_3 : WalkBound ⟨165,184,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk555_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk556_0 (pattern : Twelve) : walkGuard ⟨166,146,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk556_0 : WalkBound ⟨166,146,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk556_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk556_1 (pattern : Twelve) : walkGuard ⟨166,146,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk556_1 : WalkBound ⟨166,146,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk556_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk556_2 (pattern : Twelve) : walkGuard ⟨166,146,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk556_2 : WalkBound ⟨166,146,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk556_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk556_3 (pattern : Twelve) : walkGuard ⟨166,146,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk556_3 : WalkBound ⟨166,146,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk556_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk557_0 (pattern : Twelve) : walkGuard ⟨166,186,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk557_0 : WalkBound ⟨166,186,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk557_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk557_1 (pattern : Twelve) : walkGuard ⟨166,186,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk557_1 : WalkBound ⟨166,186,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk557_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk557_2 (pattern : Twelve) : walkGuard ⟨166,186,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk557_2 : WalkBound ⟨166,186,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk557_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk557_3 (pattern : Twelve) : walkGuard ⟨166,186,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk557_3 : WalkBound ⟨166,186,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk557_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk558_0 (pattern : Twelve) : walkGuard ⟨166,165,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk558_0 : WalkBound ⟨166,165,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk558_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk558_1 (pattern : Twelve) : walkGuard ⟨166,165,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk558_1 : WalkBound ⟨166,165,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk558_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk558_2 (pattern : Twelve) : walkGuard ⟨166,165,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk558_2 : WalkBound ⟨166,165,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk558_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk558_3 (pattern : Twelve) : walkGuard ⟨166,165,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk558_3 : WalkBound ⟨166,165,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk558_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk559_0 (pattern : Twelve) : walkGuard ⟨166,187,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk559_0 : WalkBound ⟨166,187,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk559_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk559_1 (pattern : Twelve) : walkGuard ⟨166,187,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk559_1 : WalkBound ⟨166,187,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk559_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk559_2 (pattern : Twelve) : walkGuard ⟨166,187,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk559_2 : WalkBound ⟨166,187,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk559_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk559_3 (pattern : Twelve) : walkGuard ⟨166,187,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk559_3 : WalkBound ⟨166,187,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk559_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk560_0 (pattern : Twelve) : walkGuard ⟨166,185,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk560_0 : WalkBound ⟨166,185,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk560_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk560_1 (pattern : Twelve) : walkGuard ⟨166,185,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk560_1 : WalkBound ⟨166,185,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk560_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk560_2 (pattern : Twelve) : walkGuard ⟨166,185,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk560_2 : WalkBound ⟨166,185,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk560_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk560_3 (pattern : Twelve) : walkGuard ⟨166,185,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk560_3 : WalkBound ⟨166,185,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk560_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk561_0 (pattern : Twelve) : walkGuard ⟨166,145,.northWest⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk561_0 : WalkBound ⟨166,145,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk561_0]; exact allowed)
  have checked := c9631 pattern guarded
  change d806 pattern ≤ d812 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk561_1 (pattern : Twelve) : walkGuard ⟨166,145,.northWest⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk561_1 : WalkBound ⟨166,145,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk561_1]; exact allowed)
  have checked := c9637 pattern guarded
  change d1267 pattern ≤ d1273 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk561_2 (pattern : Twelve) : walkGuard ⟨166,145,.northWest⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk561_2 : WalkBound ⟨166,145,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk561_2]; exact allowed)
  have checked := c9643 pattern guarded
  change d1636 pattern ≤ d1642 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk561_3 (pattern : Twelve) : walkGuard ⟨166,145,.northWest⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk561_3 : WalkBound ⟨166,145,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk561_3]; exact allowed)
  have checked := c9648 pattern guarded
  change d1827 pattern ≤ d1833 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk562_0 (pattern : Twelve) : walkGuard ⟨181,182,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk562_0 : WalkBound ⟨181,182,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk562_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk562_1 (pattern : Twelve) : walkGuard ⟨181,182,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk562_1 : WalkBound ⟨181,182,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk562_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
