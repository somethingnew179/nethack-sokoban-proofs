/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers07
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk100_0 (pattern : Twelve) : walkGuard ⟨47,66,.southWest⟩ 0 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk100_0 : WalkBound ⟨47,66,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_0]; exact allowed)
  have checked := c1901 pattern guarded
  change d303 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk100_1 (pattern : Twelve) : walkGuard ⟨47,66,.southWest⟩ 1 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk100_1 : WalkBound ⟨47,66,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_1]; exact allowed)
  have checked := c1958 pattern guarded
  change d979 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk100_2 (pattern : Twelve) : walkGuard ⟨47,66,.southWest⟩ 2 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk100_2 : WalkBound ⟨47,66,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_2]; exact allowed)
  have checked := c2003 pattern guarded
  change d1411 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk100_3 (pattern : Twelve) : walkGuard ⟨47,66,.southWest⟩ 3 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk100_3 : WalkBound ⟨47,66,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_3]; exact allowed)
  have checked := c2024 pattern guarded
  change d1704 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_0 (pattern : Twelve) : walkGuard ⟨47,26,.northWest⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk101_0 : WalkBound ⟨47,26,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_0]; exact allowed)
  have checked := c959 pattern guarded
  change d303 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_1 (pattern : Twelve) : walkGuard ⟨47,26,.northWest⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk101_1 : WalkBound ⟨47,26,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_1]; exact allowed)
  have checked := c1042 pattern guarded
  change d979 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_2 (pattern : Twelve) : walkGuard ⟨47,26,.northWest⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk101_2 : WalkBound ⟨47,26,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_2]; exact allowed)
  have checked := c1101 pattern guarded
  change d1411 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_3 (pattern : Twelve) : walkGuard ⟨47,26,.northWest⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk101_3 : WalkBound ⟨47,26,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_3]; exact allowed)
  have checked := c1130 pattern guarded
  change d1704 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_0 (pattern : Twelve) : walkGuard ⟨48,28,.north⟩ 0 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk102_0 : WalkBound ⟨48,28,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_0]; exact allowed)
  have checked := c2084 pattern guarded
  change d344 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_1 (pattern : Twelve) : walkGuard ⟨48,28,.north⟩ 1 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk102_1 : WalkBound ⟨48,28,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_1]; exact allowed)
  have checked := c2128 pattern guarded
  change d1010 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_2 (pattern : Twelve) : walkGuard ⟨48,28,.north⟩ 2 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk102_2 : WalkBound ⟨48,28,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_2]; exact allowed)
  have checked := c2163 pattern guarded
  change d1427 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_3 (pattern : Twelve) : walkGuard ⟨48,28,.north⟩ 3 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> rfl
theorem walk102_3 : WalkBound ⟨48,28,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_3]; exact allowed)
  have checked := c2175 pattern guarded
  change d1713 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_0 (pattern : Twelve) : walkGuard ⟨48,68,.south⟩ 0 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk103_0 : WalkBound ⟨48,68,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_0]; exact allowed)
  have checked := c2283 pattern guarded
  change d344 pattern ≤ d476 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_1 (pattern : Twelve) : walkGuard ⟨48,68,.south⟩ 1 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk103_1 : WalkBound ⟨48,68,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_1]; exact allowed)
  have checked := c2357 pattern guarded
  change d1010 pattern ≤ d1104 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_2 (pattern : Twelve) : walkGuard ⟨48,68,.south⟩ 2 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk103_2 : WalkBound ⟨48,68,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_2]; exact allowed)
  have checked := c2392 pattern guarded
  change d1427 pattern ≤ d1492 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_3 (pattern : Twelve) : walkGuard ⟨48,68,.south⟩ 3 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk103_3 : WalkBound ⟨48,68,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_3]; exact allowed)
  have checked := c2416 pattern guarded
  change d1713 pattern ≤ d1744 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_0 (pattern : Twelve) : walkGuard ⟨48,47,.west⟩ 0 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk104_0 : WalkBound ⟨48,47,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_0]; exact allowed)
  have checked := c2470 pattern guarded
  change d344 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_1 (pattern : Twelve) : walkGuard ⟨48,47,.west⟩ 1 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk104_1 : WalkBound ⟨48,47,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_1]; exact allowed)
  have checked := c2510 pattern guarded
  change d1010 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_2 (pattern : Twelve) : walkGuard ⟨48,47,.west⟩ 2 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk104_2 : WalkBound ⟨48,47,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_2]; exact allowed)
  have checked := c2535 pattern guarded
  change d1427 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_3 (pattern : Twelve) : walkGuard ⟨48,47,.west⟩ 3 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk104_3 : WalkBound ⟨48,47,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_3]; exact allowed)
  have checked := c2545 pattern guarded
  change d1713 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk105_0 (pattern : Twelve) : walkGuard ⟨48,67,.southWest⟩ 0 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk105_0 : WalkBound ⟨48,67,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_0]; exact allowed)
  have checked := c2661 pattern guarded
  change d344 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk105_1 (pattern : Twelve) : walkGuard ⟨48,67,.southWest⟩ 1 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk105_1 : WalkBound ⟨48,67,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_1]; exact allowed)
  have checked := c2745 pattern guarded
  change d1010 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk105_2 (pattern : Twelve) : walkGuard ⟨48,67,.southWest⟩ 2 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk105_2 : WalkBound ⟨48,67,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_2]; exact allowed)
  have checked := c2790 pattern guarded
  change d1427 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk105_3 (pattern : Twelve) : walkGuard ⟨48,67,.southWest⟩ 3 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk105_3 : WalkBound ⟨48,67,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_3]; exact allowed)
  have checked := c2823 pattern guarded
  change d1713 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_0 (pattern : Twelve) : walkGuard ⟨48,27,.northWest⟩ 0 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk106_0 : WalkBound ⟨48,27,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_0]; exact allowed)
  have checked := c2084 pattern guarded
  change d344 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_1 (pattern : Twelve) : walkGuard ⟨48,27,.northWest⟩ 1 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk106_1 : WalkBound ⟨48,27,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_1]; exact allowed)
  have checked := c2128 pattern guarded
  change d1010 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_2 (pattern : Twelve) : walkGuard ⟨48,27,.northWest⟩ 2 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk106_2 : WalkBound ⟨48,27,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_2]; exact allowed)
  have checked := c2163 pattern guarded
  change d1427 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_3 (pattern : Twelve) : walkGuard ⟨48,27,.northWest⟩ 3 pattern = decide (d1839 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk106_3 : WalkBound ⟨48,27,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1839 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_3]; exact allowed)
  have checked := c2175 pattern guarded
  change d1713 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_0 (pattern : Twelve) : walkGuard ⟨50,30,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk107_0 : WalkBound ⟨50,30,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_1 (pattern : Twelve) : walkGuard ⟨50,30,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk107_1 : WalkBound ⟨50,30,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_2 (pattern : Twelve) : walkGuard ⟨50,30,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk107_2 : WalkBound ⟨50,30,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_3 (pattern : Twelve) : walkGuard ⟨50,30,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk107_3 : WalkBound ⟨50,30,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_0 (pattern : Twelve) : walkGuard ⟨50,70,.south⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk108_0 : WalkBound ⟨50,70,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_0]; exact allowed)
  have checked := c3039 pattern guarded
  change d156 pattern ≤ d629 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_1 (pattern : Twelve) : walkGuard ⟨50,70,.south⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk108_1 : WalkBound ⟨50,70,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_1]; exact allowed)
  have checked := c3134 pattern guarded
  change d907 pattern ≤ d1182 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_2 (pattern : Twelve) : walkGuard ⟨50,70,.south⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk108_2 : WalkBound ⟨50,70,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_2]; exact allowed)
  have checked := c3206 pattern guarded
  change d1354 pattern ≤ d1556 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_3 (pattern : Twelve) : walkGuard ⟨50,70,.south⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk108_3 : WalkBound ⟨50,70,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_3]; exact allowed)
  have checked := c3244 pattern guarded
  change d1678 pattern ≤ d1779 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_0 (pattern : Twelve) : walkGuard ⟨50,31,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk109_0 : WalkBound ⟨50,31,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_1 (pattern : Twelve) : walkGuard ⟨50,31,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk109_1 : WalkBound ⟨50,31,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_2 (pattern : Twelve) : walkGuard ⟨50,31,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk109_2 : WalkBound ⟨50,31,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_3 (pattern : Twelve) : walkGuard ⟨50,31,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk109_3 : WalkBound ⟨50,31,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_0 (pattern : Twelve) : walkGuard ⟨50,71,.southEast⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk110_0 : WalkBound ⟨50,71,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_0]; exact allowed)
  have checked := c3467 pattern guarded
  change d156 pattern ≤ d777 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_1 (pattern : Twelve) : walkGuard ⟨50,71,.southEast⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk110_1 : WalkBound ⟨50,71,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_1]; exact allowed)
  have checked := c3562 pattern guarded
  change d907 pattern ≤ d1246 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_2 (pattern : Twelve) : walkGuard ⟨50,71,.southEast⟩ 2 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk110_2 : WalkBound ⟨50,71,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_2]; exact allowed)
  have checked := c3634 pattern guarded
  change d1354 pattern ≤ d1615 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_3 (pattern : Twelve) : walkGuard ⟨50,71,.southEast⟩ 3 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk110_3 : WalkBound ⟨50,71,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_3]; exact allowed)
  have checked := c3671 pattern guarded
  change d1678 pattern ≤ d1813 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_0 (pattern : Twelve) : walkGuard ⟨52,32,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk111_0 : WalkBound ⟨52,32,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_1 (pattern : Twelve) : walkGuard ⟨52,32,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk111_1 : WalkBound ⟨52,32,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_2 (pattern : Twelve) : walkGuard ⟨52,32,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk111_2 : WalkBound ⟨52,32,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_3 (pattern : Twelve) : walkGuard ⟨52,32,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk111_3 : WalkBound ⟨52,32,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk112_0 (pattern : Twelve) : walkGuard ⟨52,72,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk112_0 : WalkBound ⟨52,72,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk112_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk112_1 (pattern : Twelve) : walkGuard ⟨52,72,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk112_1 : WalkBound ⟨52,72,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk112_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
