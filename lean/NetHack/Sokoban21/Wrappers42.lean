/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers41
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk525_0 (pattern : Twelve) : walkGuard ⟨156,157,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk525_0 : WalkBound ⟨156,157,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk525_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk525_1 (pattern : Twelve) : walkGuard ⟨156,157,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk525_1 : WalkBound ⟨156,157,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk525_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk525_2 (pattern : Twelve) : walkGuard ⟨156,157,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk525_2 : WalkBound ⟨156,157,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk525_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk525_3 (pattern : Twelve) : walkGuard ⟨156,157,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk525_3 : WalkBound ⟨156,157,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk525_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk526_0 (pattern : Twelve) : walkGuard ⟨156,155,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk526_0 : WalkBound ⟨156,155,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk526_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk526_1 (pattern : Twelve) : walkGuard ⟨156,155,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk526_1 : WalkBound ⟨156,155,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk526_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk526_2 (pattern : Twelve) : walkGuard ⟨156,155,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk526_2 : WalkBound ⟨156,155,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk526_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk526_3 (pattern : Twelve) : walkGuard ⟨156,155,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk526_3 : WalkBound ⟨156,155,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk526_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk527_0 (pattern : Twelve) : walkGuard ⟨156,137,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk527_0 : WalkBound ⟨156,137,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk527_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk527_1 (pattern : Twelve) : walkGuard ⟨156,137,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk527_1 : WalkBound ⟨156,137,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk527_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk527_2 (pattern : Twelve) : walkGuard ⟨156,137,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk527_2 : WalkBound ⟨156,137,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk527_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk527_3 (pattern : Twelve) : walkGuard ⟨156,137,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk527_3 : WalkBound ⟨156,137,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk527_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk528_0 (pattern : Twelve) : walkGuard ⟨156,135,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk528_0 : WalkBound ⟨156,135,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk528_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk528_1 (pattern : Twelve) : walkGuard ⟨156,135,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk528_1 : WalkBound ⟨156,135,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk528_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk528_2 (pattern : Twelve) : walkGuard ⟨156,135,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk528_2 : WalkBound ⟨156,135,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk528_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk528_3 (pattern : Twelve) : walkGuard ⟨156,135,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk528_3 : WalkBound ⟨156,135,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk528_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk529_0 (pattern : Twelve) : walkGuard ⟨157,137,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk529_0 : WalkBound ⟨157,137,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk529_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk529_1 (pattern : Twelve) : walkGuard ⟨157,137,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk529_1 : WalkBound ⟨157,137,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk529_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk529_2 (pattern : Twelve) : walkGuard ⟨157,137,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk529_2 : WalkBound ⟨157,137,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk529_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk529_3 (pattern : Twelve) : walkGuard ⟨157,137,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk529_3 : WalkBound ⟨157,137,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk529_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk530_0 (pattern : Twelve) : walkGuard ⟨157,158,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk530_0 : WalkBound ⟨157,158,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk530_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk530_1 (pattern : Twelve) : walkGuard ⟨157,158,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk530_1 : WalkBound ⟨157,158,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk530_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk530_2 (pattern : Twelve) : walkGuard ⟨157,158,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk530_2 : WalkBound ⟨157,158,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk530_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk530_3 (pattern : Twelve) : walkGuard ⟨157,158,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk530_3 : WalkBound ⟨157,158,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk530_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk531_0 (pattern : Twelve) : walkGuard ⟨157,156,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk531_0 : WalkBound ⟨157,156,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk531_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk531_1 (pattern : Twelve) : walkGuard ⟨157,156,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk531_1 : WalkBound ⟨157,156,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk531_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk531_2 (pattern : Twelve) : walkGuard ⟨157,156,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk531_2 : WalkBound ⟨157,156,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk531_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk531_3 (pattern : Twelve) : walkGuard ⟨157,156,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk531_3 : WalkBound ⟨157,156,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk531_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk532_0 (pattern : Twelve) : walkGuard ⟨157,138,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk532_0 : WalkBound ⟨157,138,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk532_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk532_1 (pattern : Twelve) : walkGuard ⟨157,138,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk532_1 : WalkBound ⟨157,138,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk532_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk532_2 (pattern : Twelve) : walkGuard ⟨157,138,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk532_2 : WalkBound ⟨157,138,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk532_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk532_3 (pattern : Twelve) : walkGuard ⟨157,138,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk532_3 : WalkBound ⟨157,138,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk532_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk533_0 (pattern : Twelve) : walkGuard ⟨157,136,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk533_0 : WalkBound ⟨157,136,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk533_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk533_1 (pattern : Twelve) : walkGuard ⟨157,136,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk533_1 : WalkBound ⟨157,136,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk533_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk533_2 (pattern : Twelve) : walkGuard ⟨157,136,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk533_2 : WalkBound ⟨157,136,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk533_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk533_3 (pattern : Twelve) : walkGuard ⟨157,136,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk533_3 : WalkBound ⟨157,136,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk533_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk534_0 (pattern : Twelve) : walkGuard ⟨158,138,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk534_0 : WalkBound ⟨158,138,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk534_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk534_1 (pattern : Twelve) : walkGuard ⟨158,138,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk534_1 : WalkBound ⟨158,138,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk534_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk534_2 (pattern : Twelve) : walkGuard ⟨158,138,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk534_2 : WalkBound ⟨158,138,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk534_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk534_3 (pattern : Twelve) : walkGuard ⟨158,138,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk534_3 : WalkBound ⟨158,138,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk534_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk535_0 (pattern : Twelve) : walkGuard ⟨158,157,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk535_0 : WalkBound ⟨158,157,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk535_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk535_1 (pattern : Twelve) : walkGuard ⟨158,157,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk535_1 : WalkBound ⟨158,157,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk535_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk535_2 (pattern : Twelve) : walkGuard ⟨158,157,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk535_2 : WalkBound ⟨158,157,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk535_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk535_3 (pattern : Twelve) : walkGuard ⟨158,157,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk535_3 : WalkBound ⟨158,157,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk535_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk536_0 (pattern : Twelve) : walkGuard ⟨158,137,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk536_0 : WalkBound ⟨158,137,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk536_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk536_1 (pattern : Twelve) : walkGuard ⟨158,137,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk536_1 : WalkBound ⟨158,137,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk536_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk536_2 (pattern : Twelve) : walkGuard ⟨158,137,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk536_2 : WalkBound ⟨158,137,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk536_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk536_3 (pattern : Twelve) : walkGuard ⟨158,137,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk536_3 : WalkBound ⟨158,137,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk536_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk537_0 (pattern : Twelve) : walkGuard ⟨162,142,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk537_0 : WalkBound ⟨162,142,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk537_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk537_1 (pattern : Twelve) : walkGuard ⟨162,142,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk537_1 : WalkBound ⟨162,142,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk537_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
