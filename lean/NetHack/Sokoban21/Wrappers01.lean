/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers00
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk12_2 (pattern : Twelve) : walkGuard ⟨23,42,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk12_2 : WalkBound ⟨23,42,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk12_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk12_3 (pattern : Twelve) : walkGuard ⟨23,42,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk12_3 : WalkBound ⟨23,42,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk12_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_0 (pattern : Twelve) : walkGuard ⟨24,25,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk13_0 : WalkBound ⟨24,25,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_1 (pattern : Twelve) : walkGuard ⟨24,25,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk13_1 : WalkBound ⟨24,25,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_2 (pattern : Twelve) : walkGuard ⟨24,25,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk13_2 : WalkBound ⟨24,25,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_3 (pattern : Twelve) : walkGuard ⟨24,25,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk13_3 : WalkBound ⟨24,25,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_0 (pattern : Twelve) : walkGuard ⟨24,44,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk14_0 : WalkBound ⟨24,44,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_1 (pattern : Twelve) : walkGuard ⟨24,44,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk14_1 : WalkBound ⟨24,44,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_2 (pattern : Twelve) : walkGuard ⟨24,44,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk14_2 : WalkBound ⟨24,44,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_3 (pattern : Twelve) : walkGuard ⟨24,44,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk14_3 : WalkBound ⟨24,44,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_0 (pattern : Twelve) : walkGuard ⟨24,23,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk15_0 : WalkBound ⟨24,23,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_1 (pattern : Twelve) : walkGuard ⟨24,23,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk15_1 : WalkBound ⟨24,23,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_2 (pattern : Twelve) : walkGuard ⟨24,23,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk15_2 : WalkBound ⟨24,23,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_3 (pattern : Twelve) : walkGuard ⟨24,23,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk15_3 : WalkBound ⟨24,23,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_0 (pattern : Twelve) : walkGuard ⟨24,45,.southEast⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk16_0 : WalkBound ⟨24,45,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_0]; exact allowed)
  have checked := c26 pattern guarded
  change d116 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_1 (pattern : Twelve) : walkGuard ⟨24,45,.southEast⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk16_1 : WalkBound ⟨24,45,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_1]; exact allowed)
  have checked := c49 pattern guarded
  change d871 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_2 (pattern : Twelve) : walkGuard ⟨24,45,.southEast⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk16_2 : WalkBound ⟨24,45,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_2]; exact allowed)
  have checked := c70 pattern guarded
  change d1323 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_3 (pattern : Twelve) : walkGuard ⟨24,45,.southEast⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk16_3 : WalkBound ⟨24,45,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_3]; exact allowed)
  have checked := c77 pattern guarded
  change d1664 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_0 (pattern : Twelve) : walkGuard ⟨24,43,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk17_0 : WalkBound ⟨24,43,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_1 (pattern : Twelve) : walkGuard ⟨24,43,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk17_1 : WalkBound ⟨24,43,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_2 (pattern : Twelve) : walkGuard ⟨24,43,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk17_2 : WalkBound ⟨24,43,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_3 (pattern : Twelve) : walkGuard ⟨24,43,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk17_3 : WalkBound ⟨24,43,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_0 (pattern : Twelve) : walkGuard ⟨25,26,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk18_0 : WalkBound ⟨25,26,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_1 (pattern : Twelve) : walkGuard ⟨25,26,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk18_1 : WalkBound ⟨25,26,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_2 (pattern : Twelve) : walkGuard ⟨25,26,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk18_2 : WalkBound ⟨25,26,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_3 (pattern : Twelve) : walkGuard ⟨25,26,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk18_3 : WalkBound ⟨25,26,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_0 (pattern : Twelve) : walkGuard ⟨25,45,.south⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk19_0 : WalkBound ⟨25,45,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_0]; exact allowed)
  have checked := c26 pattern guarded
  change d116 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_1 (pattern : Twelve) : walkGuard ⟨25,45,.south⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk19_1 : WalkBound ⟨25,45,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_1]; exact allowed)
  have checked := c49 pattern guarded
  change d871 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_2 (pattern : Twelve) : walkGuard ⟨25,45,.south⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk19_2 : WalkBound ⟨25,45,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_2]; exact allowed)
  have checked := c70 pattern guarded
  change d1323 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_3 (pattern : Twelve) : walkGuard ⟨25,45,.south⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk19_3 : WalkBound ⟨25,45,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_3]; exact allowed)
  have checked := c77 pattern guarded
  change d1664 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_0 (pattern : Twelve) : walkGuard ⟨25,24,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk20_0 : WalkBound ⟨25,24,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_1 (pattern : Twelve) : walkGuard ⟨25,24,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk20_1 : WalkBound ⟨25,24,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_2 (pattern : Twelve) : walkGuard ⟨25,24,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk20_2 : WalkBound ⟨25,24,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_3 (pattern : Twelve) : walkGuard ⟨25,24,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk20_3 : WalkBound ⟨25,24,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_0 (pattern : Twelve) : walkGuard ⟨25,44,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk21_0 : WalkBound ⟨25,44,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_1 (pattern : Twelve) : walkGuard ⟨25,44,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk21_1 : WalkBound ⟨25,44,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_2 (pattern : Twelve) : walkGuard ⟨25,44,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk21_2 : WalkBound ⟨25,44,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_3 (pattern : Twelve) : walkGuard ⟨25,44,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk21_3 : WalkBound ⟨25,44,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_0 (pattern : Twelve) : walkGuard ⟨26,27,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk22_0 : WalkBound ⟨26,27,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_1 (pattern : Twelve) : walkGuard ⟨26,27,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk22_1 : WalkBound ⟨26,27,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_2 (pattern : Twelve) : walkGuard ⟨26,27,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk22_2 : WalkBound ⟨26,27,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_3 (pattern : Twelve) : walkGuard ⟨26,27,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk22_3 : WalkBound ⟨26,27,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_0 (pattern : Twelve) : walkGuard ⟨26,25,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk23_0 : WalkBound ⟨26,25,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_1 (pattern : Twelve) : walkGuard ⟨26,25,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk23_1 : WalkBound ⟨26,25,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_2 (pattern : Twelve) : walkGuard ⟨26,25,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk23_2 : WalkBound ⟨26,25,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_3 (pattern : Twelve) : walkGuard ⟨26,25,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk23_3 : WalkBound ⟨26,25,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_0 (pattern : Twelve) : walkGuard ⟨26,47,.southEast⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk24_0 : WalkBound ⟨26,47,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_0]; exact allowed)
  have checked := c235 pattern guarded
  change d116 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_1 (pattern : Twelve) : walkGuard ⟨26,47,.southEast⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk24_1 : WalkBound ⟨26,47,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_1]; exact allowed)
  have checked := c323 pattern guarded
  change d871 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_2 (pattern : Twelve) : walkGuard ⟨26,47,.southEast⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk24_2 : WalkBound ⟨26,47,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_2]; exact allowed)
  have checked := c387 pattern guarded
  change d1323 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_3 (pattern : Twelve) : walkGuard ⟨26,47,.southEast⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk24_3 : WalkBound ⟨26,47,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_3]; exact allowed)
  have checked := c421 pattern guarded
  change d1664 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
