/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers30
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk387_2 (pattern : Twelve) : walkGuard ⟨118,138,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk387_2 : WalkBound ⟨118,138,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk387_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk387_3 (pattern : Twelve) : walkGuard ⟨118,138,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk387_3 : WalkBound ⟨118,138,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk387_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk388_0 (pattern : Twelve) : walkGuard ⟨118,117,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk388_0 : WalkBound ⟨118,117,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk388_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk388_1 (pattern : Twelve) : walkGuard ⟨118,117,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk388_1 : WalkBound ⟨118,117,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk388_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk388_2 (pattern : Twelve) : walkGuard ⟨118,117,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk388_2 : WalkBound ⟨118,117,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk388_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk388_3 (pattern : Twelve) : walkGuard ⟨118,117,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk388_3 : WalkBound ⟨118,117,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk388_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk389_0 (pattern : Twelve) : walkGuard ⟨118,137,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk389_0 : WalkBound ⟨118,137,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk389_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk389_1 (pattern : Twelve) : walkGuard ⟨118,137,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk389_1 : WalkBound ⟨118,137,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk389_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk389_2 (pattern : Twelve) : walkGuard ⟨118,137,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk389_2 : WalkBound ⟨118,137,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk389_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk389_3 (pattern : Twelve) : walkGuard ⟨118,137,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk389_3 : WalkBound ⟨118,137,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk389_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk390_0 (pattern : Twelve) : walkGuard ⟨118,97,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk390_0 : WalkBound ⟨118,97,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk390_0]; exact allowed)
  have checked := c602 pattern guarded
  change d221 pattern ≤ d221 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk390_1 (pattern : Twelve) : walkGuard ⟨118,97,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk390_1 : WalkBound ⟨118,97,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk390_1]; exact allowed)
  have checked := c603 pattern guarded
  change d926 pattern ≤ d926 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk390_2 (pattern : Twelve) : walkGuard ⟨118,97,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk390_2 : WalkBound ⟨118,97,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk390_2]; exact allowed)
  have checked := c604 pattern guarded
  change d1367 pattern ≤ d1367 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk390_3 (pattern : Twelve) : walkGuard ⟨118,97,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk390_3 : WalkBound ⟨118,97,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk390_3]; exact allowed)
  have checked := c605 pattern guarded
  change d1685 pattern ≤ d1685 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk391_0 (pattern : Twelve) : walkGuard ⟨121,101,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk391_0 : WalkBound ⟨121,101,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk391_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk391_1 (pattern : Twelve) : walkGuard ⟨121,101,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk391_1 : WalkBound ⟨121,101,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk391_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk391_2 (pattern : Twelve) : walkGuard ⟨121,101,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk391_2 : WalkBound ⟨121,101,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk391_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk391_3 (pattern : Twelve) : walkGuard ⟨121,101,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk391_3 : WalkBound ⟨121,101,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk391_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk392_0 (pattern : Twelve) : walkGuard ⟨121,122,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk392_0 : WalkBound ⟨121,122,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk392_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk392_1 (pattern : Twelve) : walkGuard ⟨121,122,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk392_1 : WalkBound ⟨121,122,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk392_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk392_2 (pattern : Twelve) : walkGuard ⟨121,122,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk392_2 : WalkBound ⟨121,122,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk392_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk392_3 (pattern : Twelve) : walkGuard ⟨121,122,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk392_3 : WalkBound ⟨121,122,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk392_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk393_0 (pattern : Twelve) : walkGuard ⟨121,141,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk393_0 : WalkBound ⟨121,141,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk393_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk393_1 (pattern : Twelve) : walkGuard ⟨121,141,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk393_1 : WalkBound ⟨121,141,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk393_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk393_2 (pattern : Twelve) : walkGuard ⟨121,141,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk393_2 : WalkBound ⟨121,141,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk393_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk393_3 (pattern : Twelve) : walkGuard ⟨121,141,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk393_3 : WalkBound ⟨121,141,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk393_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk394_0 (pattern : Twelve) : walkGuard ⟨121,102,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk394_0 : WalkBound ⟨121,102,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk394_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk394_1 (pattern : Twelve) : walkGuard ⟨121,102,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk394_1 : WalkBound ⟨121,102,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk394_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk394_2 (pattern : Twelve) : walkGuard ⟨121,102,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk394_2 : WalkBound ⟨121,102,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk394_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk394_3 (pattern : Twelve) : walkGuard ⟨121,102,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk394_3 : WalkBound ⟨121,102,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk394_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk395_0 (pattern : Twelve) : walkGuard ⟨121,142,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk395_0 : WalkBound ⟨121,142,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk395_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk395_1 (pattern : Twelve) : walkGuard ⟨121,142,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk395_1 : WalkBound ⟨121,142,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk395_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk395_2 (pattern : Twelve) : walkGuard ⟨121,142,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk395_2 : WalkBound ⟨121,142,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk395_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk395_3 (pattern : Twelve) : walkGuard ⟨121,142,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk395_3 : WalkBound ⟨121,142,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk395_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk396_0 (pattern : Twelve) : walkGuard ⟨122,102,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk396_0 : WalkBound ⟨122,102,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk396_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk396_1 (pattern : Twelve) : walkGuard ⟨122,102,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk396_1 : WalkBound ⟨122,102,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk396_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk396_2 (pattern : Twelve) : walkGuard ⟨122,102,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk396_2 : WalkBound ⟨122,102,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk396_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk396_3 (pattern : Twelve) : walkGuard ⟨122,102,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk396_3 : WalkBound ⟨122,102,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk396_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk397_0 (pattern : Twelve) : walkGuard ⟨122,123,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk397_0 : WalkBound ⟨122,123,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk397_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk397_1 (pattern : Twelve) : walkGuard ⟨122,123,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk397_1 : WalkBound ⟨122,123,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk397_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk397_2 (pattern : Twelve) : walkGuard ⟨122,123,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk397_2 : WalkBound ⟨122,123,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk397_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk397_3 (pattern : Twelve) : walkGuard ⟨122,123,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk397_3 : WalkBound ⟨122,123,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk397_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk398_0 (pattern : Twelve) : walkGuard ⟨122,142,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk398_0 : WalkBound ⟨122,142,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk398_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk398_1 (pattern : Twelve) : walkGuard ⟨122,142,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk398_1 : WalkBound ⟨122,142,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk398_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk398_2 (pattern : Twelve) : walkGuard ⟨122,142,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk398_2 : WalkBound ⟨122,142,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk398_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk398_3 (pattern : Twelve) : walkGuard ⟨122,142,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk398_3 : WalkBound ⟨122,142,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk398_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk399_0 (pattern : Twelve) : walkGuard ⟨122,121,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk399_0 : WalkBound ⟨122,121,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk399_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk399_1 (pattern : Twelve) : walkGuard ⟨122,121,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk399_1 : WalkBound ⟨122,121,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk399_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk399_2 (pattern : Twelve) : walkGuard ⟨122,121,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk399_2 : WalkBound ⟨122,121,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk399_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk399_3 (pattern : Twelve) : walkGuard ⟨122,121,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk399_3 : WalkBound ⟨122,121,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk399_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
