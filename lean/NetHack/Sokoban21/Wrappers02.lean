/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers01
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk25_0 (pattern : Twelve) : walkGuard ⟨26,45,.southWest⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk25_0 : WalkBound ⟨26,45,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_0]; exact allowed)
  have checked := c26 pattern guarded
  change d116 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk25_1 (pattern : Twelve) : walkGuard ⟨26,45,.southWest⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk25_1 : WalkBound ⟨26,45,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_1]; exact allowed)
  have checked := c49 pattern guarded
  change d871 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk25_2 (pattern : Twelve) : walkGuard ⟨26,45,.southWest⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk25_2 : WalkBound ⟨26,45,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_2]; exact allowed)
  have checked := c70 pattern guarded
  change d1323 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk25_3 (pattern : Twelve) : walkGuard ⟨26,45,.southWest⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk25_3 : WalkBound ⟨26,45,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_3]; exact allowed)
  have checked := c77 pattern guarded
  change d1664 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_0 (pattern : Twelve) : walkGuard ⟨27,28,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk26_0 : WalkBound ⟨27,28,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_1 (pattern : Twelve) : walkGuard ⟨27,28,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk26_1 : WalkBound ⟨27,28,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_2 (pattern : Twelve) : walkGuard ⟨27,28,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk26_2 : WalkBound ⟨27,28,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_3 (pattern : Twelve) : walkGuard ⟨27,28,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk26_3 : WalkBound ⟨27,28,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_0 (pattern : Twelve) : walkGuard ⟨27,47,.south⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk27_0 : WalkBound ⟨27,47,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_0]; exact allowed)
  have checked := c235 pattern guarded
  change d116 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_1 (pattern : Twelve) : walkGuard ⟨27,47,.south⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk27_1 : WalkBound ⟨27,47,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_1]; exact allowed)
  have checked := c323 pattern guarded
  change d871 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_2 (pattern : Twelve) : walkGuard ⟨27,47,.south⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk27_2 : WalkBound ⟨27,47,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_2]; exact allowed)
  have checked := c387 pattern guarded
  change d1323 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_3 (pattern : Twelve) : walkGuard ⟨27,47,.south⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk27_3 : WalkBound ⟨27,47,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_3]; exact allowed)
  have checked := c421 pattern guarded
  change d1664 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_0 (pattern : Twelve) : walkGuard ⟨27,26,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk28_0 : WalkBound ⟨27,26,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_1 (pattern : Twelve) : walkGuard ⟨27,26,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk28_1 : WalkBound ⟨27,26,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_2 (pattern : Twelve) : walkGuard ⟨27,26,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk28_2 : WalkBound ⟨27,26,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_3 (pattern : Twelve) : walkGuard ⟨27,26,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk28_3 : WalkBound ⟨27,26,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_0 (pattern : Twelve) : walkGuard ⟨27,48,.southEast⟩ 0 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk29_0 : WalkBound ⟨27,48,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_0]; exact allowed)
  have checked := c491 pattern guarded
  change d116 pattern ≤ d344 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_1 (pattern : Twelve) : walkGuard ⟨27,48,.southEast⟩ 1 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk29_1 : WalkBound ⟨27,48,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_1]; exact allowed)
  have checked := c542 pattern guarded
  change d871 pattern ≤ d1010 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_2 (pattern : Twelve) : walkGuard ⟨27,48,.southEast⟩ 2 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk29_2 : WalkBound ⟨27,48,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_2]; exact allowed)
  have checked := c581 pattern guarded
  change d1323 pattern ≤ d1427 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_3 (pattern : Twelve) : walkGuard ⟨27,48,.southEast⟩ 3 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk29_3 : WalkBound ⟨27,48,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_3]; exact allowed)
  have checked := c597 pattern guarded
  change d1664 pattern ≤ d1713 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_0 (pattern : Twelve) : walkGuard ⟨28,48,.south⟩ 0 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk30_0 : WalkBound ⟨28,48,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_0]; exact allowed)
  have checked := c491 pattern guarded
  change d116 pattern ≤ d344 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_1 (pattern : Twelve) : walkGuard ⟨28,48,.south⟩ 1 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk30_1 : WalkBound ⟨28,48,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_1]; exact allowed)
  have checked := c542 pattern guarded
  change d871 pattern ≤ d1010 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_2 (pattern : Twelve) : walkGuard ⟨28,48,.south⟩ 2 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk30_2 : WalkBound ⟨28,48,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_2]; exact allowed)
  have checked := c581 pattern guarded
  change d1323 pattern ≤ d1427 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_3 (pattern : Twelve) : walkGuard ⟨28,48,.south⟩ 3 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk30_3 : WalkBound ⟨28,48,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_3]; exact allowed)
  have checked := c597 pattern guarded
  change d1664 pattern ≤ d1713 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_0 (pattern : Twelve) : walkGuard ⟨28,27,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk31_0 : WalkBound ⟨28,27,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_1 (pattern : Twelve) : walkGuard ⟨28,27,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk31_1 : WalkBound ⟨28,27,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_2 (pattern : Twelve) : walkGuard ⟨28,27,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk31_2 : WalkBound ⟨28,27,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_3 (pattern : Twelve) : walkGuard ⟨28,27,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk31_3 : WalkBound ⟨28,27,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_0 (pattern : Twelve) : walkGuard ⟨28,47,.southWest⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk32_0 : WalkBound ⟨28,47,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_0]; exact allowed)
  have checked := c235 pattern guarded
  change d116 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_1 (pattern : Twelve) : walkGuard ⟨28,47,.southWest⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk32_1 : WalkBound ⟨28,47,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_1]; exact allowed)
  have checked := c323 pattern guarded
  change d871 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_2 (pattern : Twelve) : walkGuard ⟨28,47,.southWest⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk32_2 : WalkBound ⟨28,47,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_2]; exact allowed)
  have checked := c387 pattern guarded
  change d1323 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_3 (pattern : Twelve) : walkGuard ⟨28,47,.southWest⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk32_3 : WalkBound ⟨28,47,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_3]; exact allowed)
  have checked := c421 pattern guarded
  change d1664 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_0 (pattern : Twelve) : walkGuard ⟨30,31,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk33_0 : WalkBound ⟨30,31,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_1 (pattern : Twelve) : walkGuard ⟨30,31,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk33_1 : WalkBound ⟨30,31,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_2 (pattern : Twelve) : walkGuard ⟨30,31,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk33_2 : WalkBound ⟨30,31,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_3 (pattern : Twelve) : walkGuard ⟨30,31,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk33_3 : WalkBound ⟨30,31,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_0 (pattern : Twelve) : walkGuard ⟨30,50,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk34_0 : WalkBound ⟨30,50,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_1 (pattern : Twelve) : walkGuard ⟨30,50,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk34_1 : WalkBound ⟨30,50,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_2 (pattern : Twelve) : walkGuard ⟨30,50,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk34_2 : WalkBound ⟨30,50,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_3 (pattern : Twelve) : walkGuard ⟨30,50,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk34_3 : WalkBound ⟨30,50,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk35_0 (pattern : Twelve) : walkGuard ⟨31,32,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk35_0 : WalkBound ⟨31,32,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk35_1 (pattern : Twelve) : walkGuard ⟨31,32,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk35_1 : WalkBound ⟨31,32,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk35_2 (pattern : Twelve) : walkGuard ⟨31,32,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk35_2 : WalkBound ⟨31,32,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk35_3 (pattern : Twelve) : walkGuard ⟨31,32,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk35_3 : WalkBound ⟨31,32,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_0 (pattern : Twelve) : walkGuard ⟨31,30,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk36_0 : WalkBound ⟨31,30,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_1 (pattern : Twelve) : walkGuard ⟨31,30,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk36_1 : WalkBound ⟨31,30,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_2 (pattern : Twelve) : walkGuard ⟨31,30,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk36_2 : WalkBound ⟨31,30,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_3 (pattern : Twelve) : walkGuard ⟨31,30,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk36_3 : WalkBound ⟨31,30,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk37_0 (pattern : Twelve) : walkGuard ⟨31,52,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk37_0 : WalkBound ⟨31,52,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk37_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk37_1 (pattern : Twelve) : walkGuard ⟨31,52,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk37_1 : WalkBound ⟨31,52,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk37_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
