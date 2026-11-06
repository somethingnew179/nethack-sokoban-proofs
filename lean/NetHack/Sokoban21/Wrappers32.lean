/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers31
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk400_0 (pattern : Twelve) : walkGuard ⟨122,103,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk400_0 : WalkBound ⟨122,103,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk400_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk400_1 (pattern : Twelve) : walkGuard ⟨122,103,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk400_1 : WalkBound ⟨122,103,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk400_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk400_2 (pattern : Twelve) : walkGuard ⟨122,103,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk400_2 : WalkBound ⟨122,103,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk400_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk400_3 (pattern : Twelve) : walkGuard ⟨122,103,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk400_3 : WalkBound ⟨122,103,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk400_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk401_0 (pattern : Twelve) : walkGuard ⟨122,143,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk401_0 : WalkBound ⟨122,143,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk401_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk401_1 (pattern : Twelve) : walkGuard ⟨122,143,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk401_1 : WalkBound ⟨122,143,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk401_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk401_2 (pattern : Twelve) : walkGuard ⟨122,143,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk401_2 : WalkBound ⟨122,143,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk401_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk401_3 (pattern : Twelve) : walkGuard ⟨122,143,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk401_3 : WalkBound ⟨122,143,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk401_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk402_0 (pattern : Twelve) : walkGuard ⟨122,141,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk402_0 : WalkBound ⟨122,141,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk402_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk402_1 (pattern : Twelve) : walkGuard ⟨122,141,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk402_1 : WalkBound ⟨122,141,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk402_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk402_2 (pattern : Twelve) : walkGuard ⟨122,141,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk402_2 : WalkBound ⟨122,141,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk402_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk402_3 (pattern : Twelve) : walkGuard ⟨122,141,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk402_3 : WalkBound ⟨122,141,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk402_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk403_0 (pattern : Twelve) : walkGuard ⟨122,101,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk403_0 : WalkBound ⟨122,101,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk403_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk403_1 (pattern : Twelve) : walkGuard ⟨122,101,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk403_1 : WalkBound ⟨122,101,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk403_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk403_2 (pattern : Twelve) : walkGuard ⟨122,101,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk403_2 : WalkBound ⟨122,101,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk403_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk403_3 (pattern : Twelve) : walkGuard ⟨122,101,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk403_3 : WalkBound ⟨122,101,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk403_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk404_0 (pattern : Twelve) : walkGuard ⟨123,103,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk404_0 : WalkBound ⟨123,103,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk404_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk404_1 (pattern : Twelve) : walkGuard ⟨123,103,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk404_1 : WalkBound ⟨123,103,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk404_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk404_2 (pattern : Twelve) : walkGuard ⟨123,103,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk404_2 : WalkBound ⟨123,103,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk404_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk404_3 (pattern : Twelve) : walkGuard ⟨123,103,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk404_3 : WalkBound ⟨123,103,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk404_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk405_0 (pattern : Twelve) : walkGuard ⟨123,143,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk405_0 : WalkBound ⟨123,143,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk405_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk405_1 (pattern : Twelve) : walkGuard ⟨123,143,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk405_1 : WalkBound ⟨123,143,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk405_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk405_2 (pattern : Twelve) : walkGuard ⟨123,143,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk405_2 : WalkBound ⟨123,143,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk405_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk405_3 (pattern : Twelve) : walkGuard ⟨123,143,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk405_3 : WalkBound ⟨123,143,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk405_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk406_0 (pattern : Twelve) : walkGuard ⟨123,122,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk406_0 : WalkBound ⟨123,122,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk406_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk406_1 (pattern : Twelve) : walkGuard ⟨123,122,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk406_1 : WalkBound ⟨123,122,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk406_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk406_2 (pattern : Twelve) : walkGuard ⟨123,122,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk406_2 : WalkBound ⟨123,122,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk406_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk406_3 (pattern : Twelve) : walkGuard ⟨123,122,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk406_3 : WalkBound ⟨123,122,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk406_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk407_0 (pattern : Twelve) : walkGuard ⟨123,142,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk407_0 : WalkBound ⟨123,142,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk407_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk407_1 (pattern : Twelve) : walkGuard ⟨123,142,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk407_1 : WalkBound ⟨123,142,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk407_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk407_2 (pattern : Twelve) : walkGuard ⟨123,142,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk407_2 : WalkBound ⟨123,142,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk407_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk407_3 (pattern : Twelve) : walkGuard ⟨123,142,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk407_3 : WalkBound ⟨123,142,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk407_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk408_0 (pattern : Twelve) : walkGuard ⟨123,102,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk408_0 : WalkBound ⟨123,102,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk408_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk408_1 (pattern : Twelve) : walkGuard ⟨123,102,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk408_1 : WalkBound ⟨123,102,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk408_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk408_2 (pattern : Twelve) : walkGuard ⟨123,102,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk408_2 : WalkBound ⟨123,102,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk408_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk408_3 (pattern : Twelve) : walkGuard ⟨123,102,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk408_3 : WalkBound ⟨123,102,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk408_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk409_0 (pattern : Twelve) : walkGuard ⟨125,126,.east⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk409_0 : WalkBound ⟨125,126,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk409_0]; exact allowed)
  have checked := c9612 pattern guarded
  change d806 pattern ≤ d809 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk409_1 (pattern : Twelve) : walkGuard ⟨125,126,.east⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk409_1 : WalkBound ⟨125,126,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk409_1]; exact allowed)
  have checked := c9617 pattern guarded
  change d1267 pattern ≤ d1270 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk409_2 (pattern : Twelve) : walkGuard ⟨125,126,.east⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk409_2 : WalkBound ⟨125,126,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk409_2]; exact allowed)
  have checked := c9622 pattern guarded
  change d1636 pattern ≤ d1639 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk409_3 (pattern : Twelve) : walkGuard ⟨125,126,.east⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk409_3 : WalkBound ⟨125,126,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk409_3]; exact allowed)
  have checked := c9625 pattern guarded
  change d1827 pattern ≤ d1830 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk410_0 (pattern : Twelve) : walkGuard ⟨125,145,.south⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk410_0 : WalkBound ⟨125,145,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk410_0]; exact allowed)
  have checked := c9631 pattern guarded
  change d806 pattern ≤ d812 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk410_1 (pattern : Twelve) : walkGuard ⟨125,145,.south⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk410_1 : WalkBound ⟨125,145,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk410_1]; exact allowed)
  have checked := c9637 pattern guarded
  change d1267 pattern ≤ d1273 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk410_2 (pattern : Twelve) : walkGuard ⟨125,145,.south⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk410_2 : WalkBound ⟨125,145,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk410_2]; exact allowed)
  have checked := c9643 pattern guarded
  change d1636 pattern ≤ d1642 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk410_3 (pattern : Twelve) : walkGuard ⟨125,145,.south⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk410_3 : WalkBound ⟨125,145,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk410_3]; exact allowed)
  have checked := c9648 pattern guarded
  change d1827 pattern ≤ d1833 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk411_0 (pattern : Twelve) : walkGuard ⟨125,106,.northEast⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk411_0 : WalkBound ⟨125,106,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk411_0]; exact allowed)
  have checked := c9653 pattern guarded
  change d806 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk411_1 (pattern : Twelve) : walkGuard ⟨125,106,.northEast⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk411_1 : WalkBound ⟨125,106,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk411_1]; exact allowed)
  have checked := c9658 pattern guarded
  change d1267 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk411_2 (pattern : Twelve) : walkGuard ⟨125,106,.northEast⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk411_2 : WalkBound ⟨125,106,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk411_2]; exact allowed)
  have checked := c9663 pattern guarded
  change d1636 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk411_3 (pattern : Twelve) : walkGuard ⟨125,106,.northEast⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk411_3 : WalkBound ⟨125,106,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk411_3]; exact allowed)
  have checked := c9666 pattern guarded
  change d1827 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk412_0 (pattern : Twelve) : walkGuard ⟨125,146,.southEast⟩ 0 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk412_0 : WalkBound ⟨125,146,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk412_0]; exact allowed)
  have checked := c9667 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk412_1 (pattern : Twelve) : walkGuard ⟨125,146,.southEast⟩ 1 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk412_1 : WalkBound ⟨125,146,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk412_1]; exact allowed)
  have checked := c9668 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
