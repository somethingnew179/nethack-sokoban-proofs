/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers35
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk450_0 (pattern : Twelve) : walkGuard ⟨135,136,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk450_0 : WalkBound ⟨135,136,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk450_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk450_1 (pattern : Twelve) : walkGuard ⟨135,136,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk450_1 : WalkBound ⟨135,136,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk450_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk450_2 (pattern : Twelve) : walkGuard ⟨135,136,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk450_2 : WalkBound ⟨135,136,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk450_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk450_3 (pattern : Twelve) : walkGuard ⟨135,136,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk450_3 : WalkBound ⟨135,136,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk450_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk451_0 (pattern : Twelve) : walkGuard ⟨135,155,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk451_0 : WalkBound ⟨135,155,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk451_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk451_1 (pattern : Twelve) : walkGuard ⟨135,155,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk451_1 : WalkBound ⟨135,155,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk451_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk451_2 (pattern : Twelve) : walkGuard ⟨135,155,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk451_2 : WalkBound ⟨135,155,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk451_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk451_3 (pattern : Twelve) : walkGuard ⟨135,155,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk451_3 : WalkBound ⟨135,155,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk451_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk452_0 (pattern : Twelve) : walkGuard ⟨135,134,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk452_0 : WalkBound ⟨135,134,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk452_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk452_1 (pattern : Twelve) : walkGuard ⟨135,134,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk452_1 : WalkBound ⟨135,134,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk452_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk452_2 (pattern : Twelve) : walkGuard ⟨135,134,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk452_2 : WalkBound ⟨135,134,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk452_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk452_3 (pattern : Twelve) : walkGuard ⟨135,134,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk452_3 : WalkBound ⟨135,134,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk452_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk453_0 (pattern : Twelve) : walkGuard ⟨135,116,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk453_0 : WalkBound ⟨135,116,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk453_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk453_1 (pattern : Twelve) : walkGuard ⟨135,116,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk453_1 : WalkBound ⟨135,116,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk453_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk453_2 (pattern : Twelve) : walkGuard ⟨135,116,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk453_2 : WalkBound ⟨135,116,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk453_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk453_3 (pattern : Twelve) : walkGuard ⟨135,116,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk453_3 : WalkBound ⟨135,116,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk453_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk454_0 (pattern : Twelve) : walkGuard ⟨135,156,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk454_0 : WalkBound ⟨135,156,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk454_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk454_1 (pattern : Twelve) : walkGuard ⟨135,156,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk454_1 : WalkBound ⟨135,156,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk454_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk454_2 (pattern : Twelve) : walkGuard ⟨135,156,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk454_2 : WalkBound ⟨135,156,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk454_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk454_3 (pattern : Twelve) : walkGuard ⟨135,156,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk454_3 : WalkBound ⟨135,156,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk454_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk455_0 (pattern : Twelve) : walkGuard ⟨135,154,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk455_0 : WalkBound ⟨135,154,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk455_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk455_1 (pattern : Twelve) : walkGuard ⟨135,154,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk455_1 : WalkBound ⟨135,154,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk455_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk455_2 (pattern : Twelve) : walkGuard ⟨135,154,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk455_2 : WalkBound ⟨135,154,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk455_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk455_3 (pattern : Twelve) : walkGuard ⟨135,154,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk455_3 : WalkBound ⟨135,154,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk455_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk456_0 (pattern : Twelve) : walkGuard ⟨135,114,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk456_0 : WalkBound ⟨135,114,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk456_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk456_1 (pattern : Twelve) : walkGuard ⟨135,114,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk456_1 : WalkBound ⟨135,114,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk456_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk456_2 (pattern : Twelve) : walkGuard ⟨135,114,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk456_2 : WalkBound ⟨135,114,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk456_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk456_3 (pattern : Twelve) : walkGuard ⟨135,114,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk456_3 : WalkBound ⟨135,114,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk456_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk457_0 (pattern : Twelve) : walkGuard ⟨136,116,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk457_0 : WalkBound ⟨136,116,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk457_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk457_1 (pattern : Twelve) : walkGuard ⟨136,116,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk457_1 : WalkBound ⟨136,116,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk457_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk457_2 (pattern : Twelve) : walkGuard ⟨136,116,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk457_2 : WalkBound ⟨136,116,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk457_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk457_3 (pattern : Twelve) : walkGuard ⟨136,116,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk457_3 : WalkBound ⟨136,116,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk457_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk458_0 (pattern : Twelve) : walkGuard ⟨136,137,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk458_0 : WalkBound ⟨136,137,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk458_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk458_1 (pattern : Twelve) : walkGuard ⟨136,137,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk458_1 : WalkBound ⟨136,137,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk458_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk458_2 (pattern : Twelve) : walkGuard ⟨136,137,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk458_2 : WalkBound ⟨136,137,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk458_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk458_3 (pattern : Twelve) : walkGuard ⟨136,137,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk458_3 : WalkBound ⟨136,137,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk458_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk459_0 (pattern : Twelve) : walkGuard ⟨136,156,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk459_0 : WalkBound ⟨136,156,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk459_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk459_1 (pattern : Twelve) : walkGuard ⟨136,156,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk459_1 : WalkBound ⟨136,156,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk459_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk459_2 (pattern : Twelve) : walkGuard ⟨136,156,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk459_2 : WalkBound ⟨136,156,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk459_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk459_3 (pattern : Twelve) : walkGuard ⟨136,156,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk459_3 : WalkBound ⟨136,156,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk459_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk460_0 (pattern : Twelve) : walkGuard ⟨136,135,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk460_0 : WalkBound ⟨136,135,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk460_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk460_1 (pattern : Twelve) : walkGuard ⟨136,135,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk460_1 : WalkBound ⟨136,135,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk460_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk460_2 (pattern : Twelve) : walkGuard ⟨136,135,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk460_2 : WalkBound ⟨136,135,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk460_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk460_3 (pattern : Twelve) : walkGuard ⟨136,135,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk460_3 : WalkBound ⟨136,135,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk460_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk461_0 (pattern : Twelve) : walkGuard ⟨136,117,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk461_0 : WalkBound ⟨136,117,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk461_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk461_1 (pattern : Twelve) : walkGuard ⟨136,117,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk461_1 : WalkBound ⟨136,117,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk461_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk461_2 (pattern : Twelve) : walkGuard ⟨136,117,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk461_2 : WalkBound ⟨136,117,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk461_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk461_3 (pattern : Twelve) : walkGuard ⟨136,117,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk461_3 : WalkBound ⟨136,117,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk461_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk462_0 (pattern : Twelve) : walkGuard ⟨136,157,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk462_0 : WalkBound ⟨136,157,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk462_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk462_1 (pattern : Twelve) : walkGuard ⟨136,157,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk462_1 : WalkBound ⟨136,157,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk462_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
