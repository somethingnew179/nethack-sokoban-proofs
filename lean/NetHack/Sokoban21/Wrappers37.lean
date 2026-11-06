/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers36
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk462_2 (pattern : Twelve) : walkGuard ⟨136,157,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk462_2 : WalkBound ⟨136,157,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk462_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk462_3 (pattern : Twelve) : walkGuard ⟨136,157,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk462_3 : WalkBound ⟨136,157,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk462_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk463_0 (pattern : Twelve) : walkGuard ⟨136,155,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk463_0 : WalkBound ⟨136,155,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk463_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk463_1 (pattern : Twelve) : walkGuard ⟨136,155,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk463_1 : WalkBound ⟨136,155,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk463_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk463_2 (pattern : Twelve) : walkGuard ⟨136,155,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk463_2 : WalkBound ⟨136,155,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk463_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk463_3 (pattern : Twelve) : walkGuard ⟨136,155,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk463_3 : WalkBound ⟨136,155,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk463_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk464_0 (pattern : Twelve) : walkGuard ⟨136,115,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk464_0 : WalkBound ⟨136,115,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk464_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk464_1 (pattern : Twelve) : walkGuard ⟨136,115,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk464_1 : WalkBound ⟨136,115,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk464_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk464_2 (pattern : Twelve) : walkGuard ⟨136,115,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk464_2 : WalkBound ⟨136,115,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk464_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk464_3 (pattern : Twelve) : walkGuard ⟨136,115,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk464_3 : WalkBound ⟨136,115,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk464_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk465_0 (pattern : Twelve) : walkGuard ⟨137,117,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk465_0 : WalkBound ⟨137,117,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk465_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk465_1 (pattern : Twelve) : walkGuard ⟨137,117,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk465_1 : WalkBound ⟨137,117,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk465_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk465_2 (pattern : Twelve) : walkGuard ⟨137,117,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk465_2 : WalkBound ⟨137,117,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk465_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk465_3 (pattern : Twelve) : walkGuard ⟨137,117,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk465_3 : WalkBound ⟨137,117,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk465_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk466_0 (pattern : Twelve) : walkGuard ⟨137,138,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk466_0 : WalkBound ⟨137,138,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk466_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk466_1 (pattern : Twelve) : walkGuard ⟨137,138,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk466_1 : WalkBound ⟨137,138,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk466_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk466_2 (pattern : Twelve) : walkGuard ⟨137,138,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk466_2 : WalkBound ⟨137,138,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk466_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk466_3 (pattern : Twelve) : walkGuard ⟨137,138,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk466_3 : WalkBound ⟨137,138,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk466_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk467_0 (pattern : Twelve) : walkGuard ⟨137,157,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk467_0 : WalkBound ⟨137,157,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk467_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk467_1 (pattern : Twelve) : walkGuard ⟨137,157,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk467_1 : WalkBound ⟨137,157,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk467_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk467_2 (pattern : Twelve) : walkGuard ⟨137,157,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk467_2 : WalkBound ⟨137,157,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk467_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk467_3 (pattern : Twelve) : walkGuard ⟨137,157,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk467_3 : WalkBound ⟨137,157,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk467_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk468_0 (pattern : Twelve) : walkGuard ⟨137,136,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk468_0 : WalkBound ⟨137,136,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk468_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk468_1 (pattern : Twelve) : walkGuard ⟨137,136,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk468_1 : WalkBound ⟨137,136,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk468_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk468_2 (pattern : Twelve) : walkGuard ⟨137,136,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk468_2 : WalkBound ⟨137,136,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk468_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk468_3 (pattern : Twelve) : walkGuard ⟨137,136,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk468_3 : WalkBound ⟨137,136,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk468_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk469_0 (pattern : Twelve) : walkGuard ⟨137,118,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk469_0 : WalkBound ⟨137,118,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk469_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk469_1 (pattern : Twelve) : walkGuard ⟨137,118,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk469_1 : WalkBound ⟨137,118,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk469_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk469_2 (pattern : Twelve) : walkGuard ⟨137,118,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk469_2 : WalkBound ⟨137,118,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk469_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk469_3 (pattern : Twelve) : walkGuard ⟨137,118,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk469_3 : WalkBound ⟨137,118,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk469_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk470_0 (pattern : Twelve) : walkGuard ⟨137,158,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk470_0 : WalkBound ⟨137,158,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk470_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk470_1 (pattern : Twelve) : walkGuard ⟨137,158,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk470_1 : WalkBound ⟨137,158,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk470_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk470_2 (pattern : Twelve) : walkGuard ⟨137,158,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk470_2 : WalkBound ⟨137,158,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk470_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk470_3 (pattern : Twelve) : walkGuard ⟨137,158,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk470_3 : WalkBound ⟨137,158,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk470_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk471_0 (pattern : Twelve) : walkGuard ⟨137,156,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk471_0 : WalkBound ⟨137,156,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk471_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk471_1 (pattern : Twelve) : walkGuard ⟨137,156,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk471_1 : WalkBound ⟨137,156,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk471_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk471_2 (pattern : Twelve) : walkGuard ⟨137,156,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk471_2 : WalkBound ⟨137,156,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk471_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk471_3 (pattern : Twelve) : walkGuard ⟨137,156,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk471_3 : WalkBound ⟨137,156,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk471_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk472_0 (pattern : Twelve) : walkGuard ⟨137,116,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk472_0 : WalkBound ⟨137,116,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk472_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk472_1 (pattern : Twelve) : walkGuard ⟨137,116,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk472_1 : WalkBound ⟨137,116,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk472_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk472_2 (pattern : Twelve) : walkGuard ⟨137,116,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk472_2 : WalkBound ⟨137,116,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk472_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk472_3 (pattern : Twelve) : walkGuard ⟨137,116,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk472_3 : WalkBound ⟨137,116,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk472_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk473_0 (pattern : Twelve) : walkGuard ⟨138,118,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk473_0 : WalkBound ⟨138,118,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk473_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk473_1 (pattern : Twelve) : walkGuard ⟨138,118,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk473_1 : WalkBound ⟨138,118,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk473_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk473_2 (pattern : Twelve) : walkGuard ⟨138,118,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk473_2 : WalkBound ⟨138,118,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk473_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk473_3 (pattern : Twelve) : walkGuard ⟨138,118,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk473_3 : WalkBound ⟨138,118,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk473_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk474_0 (pattern : Twelve) : walkGuard ⟨138,158,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk474_0 : WalkBound ⟨138,158,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk474_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk474_1 (pattern : Twelve) : walkGuard ⟨138,158,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk474_1 : WalkBound ⟨138,158,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk474_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk474_2 (pattern : Twelve) : walkGuard ⟨138,158,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk474_2 : WalkBound ⟨138,158,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk474_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk474_3 (pattern : Twelve) : walkGuard ⟨138,158,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk474_3 : WalkBound ⟨138,158,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk474_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
