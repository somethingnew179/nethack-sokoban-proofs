/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers46
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk587_2 (pattern : Twelve) : walkGuard ⟨185,205,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk587_2 : WalkBound ⟨185,205,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk587_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk587_3 (pattern : Twelve) : walkGuard ⟨185,205,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk587_3 : WalkBound ⟨185,205,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk587_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk588_0 (pattern : Twelve) : walkGuard ⟨185,184,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk588_0 : WalkBound ⟨185,184,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk588_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk588_1 (pattern : Twelve) : walkGuard ⟨185,184,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk588_1 : WalkBound ⟨185,184,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk588_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk588_2 (pattern : Twelve) : walkGuard ⟨185,184,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk588_2 : WalkBound ⟨185,184,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk588_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk588_3 (pattern : Twelve) : walkGuard ⟨185,184,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk588_3 : WalkBound ⟨185,184,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk588_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk589_0 (pattern : Twelve) : walkGuard ⟨185,166,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk589_0 : WalkBound ⟨185,166,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk589_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk589_1 (pattern : Twelve) : walkGuard ⟨185,166,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk589_1 : WalkBound ⟨185,166,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk589_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk589_2 (pattern : Twelve) : walkGuard ⟨185,166,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk589_2 : WalkBound ⟨185,166,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk589_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk589_3 (pattern : Twelve) : walkGuard ⟨185,166,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk589_3 : WalkBound ⟨185,166,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk589_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk590_0 (pattern : Twelve) : walkGuard ⟨185,206,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk590_0 : WalkBound ⟨185,206,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk590_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk590_1 (pattern : Twelve) : walkGuard ⟨185,206,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk590_1 : WalkBound ⟨185,206,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk590_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk590_2 (pattern : Twelve) : walkGuard ⟨185,206,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk590_2 : WalkBound ⟨185,206,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk590_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk590_3 (pattern : Twelve) : walkGuard ⟨185,206,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk590_3 : WalkBound ⟨185,206,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk590_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk591_0 (pattern : Twelve) : walkGuard ⟨186,166,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk591_0 : WalkBound ⟨186,166,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk591_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk591_1 (pattern : Twelve) : walkGuard ⟨186,166,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk591_1 : WalkBound ⟨186,166,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk591_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk591_2 (pattern : Twelve) : walkGuard ⟨186,166,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk591_2 : WalkBound ⟨186,166,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk591_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk591_3 (pattern : Twelve) : walkGuard ⟨186,166,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk591_3 : WalkBound ⟨186,166,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk591_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk592_0 (pattern : Twelve) : walkGuard ⟨186,187,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk592_0 : WalkBound ⟨186,187,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk592_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk592_1 (pattern : Twelve) : walkGuard ⟨186,187,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk592_1 : WalkBound ⟨186,187,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk592_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk592_2 (pattern : Twelve) : walkGuard ⟨186,187,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk592_2 : WalkBound ⟨186,187,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk592_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk592_3 (pattern : Twelve) : walkGuard ⟨186,187,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk592_3 : WalkBound ⟨186,187,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk592_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk593_0 (pattern : Twelve) : walkGuard ⟨186,206,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk593_0 : WalkBound ⟨186,206,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk593_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk593_1 (pattern : Twelve) : walkGuard ⟨186,206,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk593_1 : WalkBound ⟨186,206,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk593_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk593_2 (pattern : Twelve) : walkGuard ⟨186,206,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk593_2 : WalkBound ⟨186,206,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk593_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk593_3 (pattern : Twelve) : walkGuard ⟨186,206,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk593_3 : WalkBound ⟨186,206,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk593_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk594_0 (pattern : Twelve) : walkGuard ⟨186,185,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk594_0 : WalkBound ⟨186,185,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk594_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk594_1 (pattern : Twelve) : walkGuard ⟨186,185,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk594_1 : WalkBound ⟨186,185,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk594_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk594_2 (pattern : Twelve) : walkGuard ⟨186,185,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk594_2 : WalkBound ⟨186,185,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk594_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk594_3 (pattern : Twelve) : walkGuard ⟨186,185,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk594_3 : WalkBound ⟨186,185,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk594_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk595_0 (pattern : Twelve) : walkGuard ⟨186,205,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk595_0 : WalkBound ⟨186,205,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk595_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk595_1 (pattern : Twelve) : walkGuard ⟨186,205,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk595_1 : WalkBound ⟨186,205,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk595_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk595_2 (pattern : Twelve) : walkGuard ⟨186,205,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk595_2 : WalkBound ⟨186,205,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk595_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk595_3 (pattern : Twelve) : walkGuard ⟨186,205,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk595_3 : WalkBound ⟨186,205,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk595_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk596_0 (pattern : Twelve) : walkGuard ⟨186,165,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk596_0 : WalkBound ⟨186,165,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk596_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk596_1 (pattern : Twelve) : walkGuard ⟨186,165,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk596_1 : WalkBound ⟨186,165,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk596_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk596_2 (pattern : Twelve) : walkGuard ⟨186,165,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk596_2 : WalkBound ⟨186,165,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk596_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk596_3 (pattern : Twelve) : walkGuard ⟨186,165,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk596_3 : WalkBound ⟨186,165,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk596_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk597_0 (pattern : Twelve) : walkGuard ⟨187,188,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk597_0 : WalkBound ⟨187,188,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk597_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk597_1 (pattern : Twelve) : walkGuard ⟨187,188,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk597_1 : WalkBound ⟨187,188,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk597_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk597_2 (pattern : Twelve) : walkGuard ⟨187,188,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk597_2 : WalkBound ⟨187,188,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk597_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk597_3 (pattern : Twelve) : walkGuard ⟨187,188,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk597_3 : WalkBound ⟨187,188,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk597_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk598_0 (pattern : Twelve) : walkGuard ⟨187,186,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk598_0 : WalkBound ⟨187,186,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk598_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk598_1 (pattern : Twelve) : walkGuard ⟨187,186,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk598_1 : WalkBound ⟨187,186,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk598_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk598_2 (pattern : Twelve) : walkGuard ⟨187,186,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk598_2 : WalkBound ⟨187,186,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk598_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk598_3 (pattern : Twelve) : walkGuard ⟨187,186,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk598_3 : WalkBound ⟨187,186,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk598_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk599_0 (pattern : Twelve) : walkGuard ⟨187,206,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk599_0 : WalkBound ⟨187,206,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk599_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk599_1 (pattern : Twelve) : walkGuard ⟨187,206,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk599_1 : WalkBound ⟨187,206,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk599_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk599_2 (pattern : Twelve) : walkGuard ⟨187,206,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk599_2 : WalkBound ⟨187,206,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk599_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk599_3 (pattern : Twelve) : walkGuard ⟨187,206,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk599_3 : WalkBound ⟨187,206,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk599_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
