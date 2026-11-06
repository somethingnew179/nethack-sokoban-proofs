/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers13
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk175_0 (pattern : Twelve) : walkGuard ⟨66,45,.northWest⟩ 0 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk175_0 : WalkBound ⟨66,45,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk175_0]; exact allowed)
  have checked := c4926 pattern guarded
  change d365 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk175_1 (pattern : Twelve) : walkGuard ⟨66,45,.northWest⟩ 1 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk175_1 : WalkBound ⟨66,45,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk175_1]; exact allowed)
  have checked := c4940 pattern guarded
  change d1029 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk175_2 (pattern : Twelve) : walkGuard ⟨66,45,.northWest⟩ 2 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk175_2 : WalkBound ⟨66,45,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk175_2]; exact allowed)
  have checked := c4953 pattern guarded
  change d1443 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk175_3 (pattern : Twelve) : walkGuard ⟨66,45,.northWest⟩ 3 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk175_3 : WalkBound ⟨66,45,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk175_3]; exact allowed)
  have checked := c4956 pattern guarded
  change d1715 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk176_0 (pattern : Twelve) : walkGuard ⟨67,47,.north⟩ 0 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk176_0 : WalkBound ⟨67,47,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk176_0]; exact allowed)
  have checked := c5086 pattern guarded
  change d424 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk176_1 (pattern : Twelve) : walkGuard ⟨67,47,.north⟩ 1 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk176_1 : WalkBound ⟨67,47,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk176_1]; exact allowed)
  have checked := c5158 pattern guarded
  change d1069 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk176_2 (pattern : Twelve) : walkGuard ⟨67,47,.north⟩ 2 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk176_2 : WalkBound ⟨67,47,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk176_2]; exact allowed)
  have checked := c5210 pattern guarded
  change d1471 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk176_3 (pattern : Twelve) : walkGuard ⟨67,47,.north⟩ 3 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk176_3 : WalkBound ⟨67,47,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk176_3]; exact allowed)
  have checked := c5242 pattern guarded
  change d1729 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk177_0 (pattern : Twelve) : walkGuard ⟨67,68,.east⟩ 0 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk177_0 : WalkBound ⟨67,68,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk177_0]; exact allowed)
  have checked := c5345 pattern guarded
  change d424 pattern ≤ d476 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk177_1 (pattern : Twelve) : walkGuard ⟨67,68,.east⟩ 1 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk177_1 : WalkBound ⟨67,68,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk177_1]; exact allowed)
  have checked := c5409 pattern guarded
  change d1069 pattern ≤ d1104 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk177_2 (pattern : Twelve) : walkGuard ⟨67,68,.east⟩ 2 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk177_2 : WalkBound ⟨67,68,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk177_2]; exact allowed)
  have checked := c5453 pattern guarded
  change d1471 pattern ≤ d1492 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk177_3 (pattern : Twelve) : walkGuard ⟨67,68,.east⟩ 3 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk177_3 : WalkBound ⟨67,68,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk177_3]; exact allowed)
  have checked := c5478 pattern guarded
  change d1729 pattern ≤ d1744 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk178_0 (pattern : Twelve) : walkGuard ⟨67,87,.south⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk178_0 : WalkBound ⟨67,87,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk178_0]; exact allowed)
  have checked := c5570 pattern guarded
  change d424 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk178_1 (pattern : Twelve) : walkGuard ⟨67,87,.south⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk178_1 : WalkBound ⟨67,87,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk178_1]; exact allowed)
  have checked := c5646 pattern guarded
  change d1069 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk178_2 (pattern : Twelve) : walkGuard ⟨67,87,.south⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk178_2 : WalkBound ⟨67,87,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk178_2]; exact allowed)
  have checked := c5701 pattern guarded
  change d1471 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk178_3 (pattern : Twelve) : walkGuard ⟨67,87,.south⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem walk178_3 : WalkBound ⟨67,87,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk178_3]; exact allowed)
  have checked := c5735 pattern guarded
  change d1729 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk179_0 (pattern : Twelve) : walkGuard ⟨67,66,.west⟩ 0 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk179_0 : WalkBound ⟨67,66,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk179_0]; exact allowed)
  have checked := c5783 pattern guarded
  change d424 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk179_1 (pattern : Twelve) : walkGuard ⟨67,66,.west⟩ 1 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk179_1 : WalkBound ⟨67,66,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk179_1]; exact allowed)
  have checked := c5820 pattern guarded
  change d1069 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk179_2 (pattern : Twelve) : walkGuard ⟨67,66,.west⟩ 2 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk179_2 : WalkBound ⟨67,66,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk179_2]; exact allowed)
  have checked := c5850 pattern guarded
  change d1471 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk179_3 (pattern : Twelve) : walkGuard ⟨67,66,.west⟩ 3 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk179_3 : WalkBound ⟨67,66,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk179_3]; exact allowed)
  have checked := c5862 pattern guarded
  change d1729 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk180_0 (pattern : Twelve) : walkGuard ⟨67,48,.northEast⟩ 0 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk180_0 : WalkBound ⟨67,48,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk180_0]; exact allowed)
  have checked := c5962 pattern guarded
  change d424 pattern ≤ d344 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk180_1 (pattern : Twelve) : walkGuard ⟨67,48,.northEast⟩ 1 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk180_1 : WalkBound ⟨67,48,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk180_1]; exact allowed)
  have checked := c6038 pattern guarded
  change d1069 pattern ≤ d1010 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk180_2 (pattern : Twelve) : walkGuard ⟨67,48,.northEast⟩ 2 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk180_2 : WalkBound ⟨67,48,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk180_2]; exact allowed)
  have checked := c6076 pattern guarded
  change d1471 pattern ≤ d1427 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk180_3 (pattern : Twelve) : walkGuard ⟨67,48,.northEast⟩ 3 pattern = decide (d1864 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk180_3 : WalkBound ⟨67,48,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1864 pattern = 1 := of_decide_eq_true (by rw [← guard_walk180_3]; exact allowed)
  have checked := c6103 pattern guarded
  change d1729 pattern ≤ d1713 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk181_0 (pattern : Twelve) : walkGuard ⟨67,88,.southEast⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk181_0 : WalkBound ⟨67,88,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk181_0]; exact allowed)
  have checked := c5570 pattern guarded
  change d424 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk181_1 (pattern : Twelve) : walkGuard ⟨67,88,.southEast⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk181_1 : WalkBound ⟨67,88,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk181_1]; exact allowed)
  have checked := c5646 pattern guarded
  change d1069 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk181_2 (pattern : Twelve) : walkGuard ⟨67,88,.southEast⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk181_2 : WalkBound ⟨67,88,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk181_2]; exact allowed)
  have checked := c5701 pattern guarded
  change d1471 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk181_3 (pattern : Twelve) : walkGuard ⟨67,88,.southEast⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk181_3 : WalkBound ⟨67,88,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk181_3]; exact allowed)
  have checked := c5735 pattern guarded
  change d1729 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk182_0 (pattern : Twelve) : walkGuard ⟨68,48,.north⟩ 0 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk182_0 : WalkBound ⟨68,48,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk182_0]; exact allowed)
  have checked := c6207 pattern guarded
  change d476 pattern ≤ d344 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk182_1 (pattern : Twelve) : walkGuard ⟨68,48,.north⟩ 1 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk182_1 : WalkBound ⟨68,48,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk182_1]; exact allowed)
  have checked := c6281 pattern guarded
  change d1104 pattern ≤ d1010 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk182_2 (pattern : Twelve) : walkGuard ⟨68,48,.north⟩ 2 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk182_2 : WalkBound ⟨68,48,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk182_2]; exact allowed)
  have checked := c6314 pattern guarded
  change d1492 pattern ≤ d1427 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk182_3 (pattern : Twelve) : walkGuard ⟨68,48,.north⟩ 3 pattern = decide (d1858 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem walk182_3 : WalkBound ⟨68,48,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1858 pattern = 1 := of_decide_eq_true (by rw [← guard_walk182_3]; exact allowed)
  have checked := c6335 pattern guarded
  change d1744 pattern ≤ d1713 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk183_0 (pattern : Twelve) : walkGuard ⟨68,88,.south⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk183_0 : WalkBound ⟨68,88,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk183_0]; exact allowed)
  have checked := c6410 pattern guarded
  change d476 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk183_1 (pattern : Twelve) : walkGuard ⟨68,88,.south⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk183_1 : WalkBound ⟨68,88,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk183_1]; exact allowed)
  have checked := c6465 pattern guarded
  change d1104 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk183_2 (pattern : Twelve) : walkGuard ⟨68,88,.south⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk183_2 : WalkBound ⟨68,88,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk183_2]; exact allowed)
  have checked := c6504 pattern guarded
  change d1492 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk183_3 (pattern : Twelve) : walkGuard ⟨68,88,.south⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk183_3 : WalkBound ⟨68,88,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk183_3]; exact allowed)
  have checked := c6530 pattern guarded
  change d1744 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk184_0 (pattern : Twelve) : walkGuard ⟨68,67,.west⟩ 0 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk184_0 : WalkBound ⟨68,67,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk184_0]; exact allowed)
  have checked := c6613 pattern guarded
  change d476 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk184_1 (pattern : Twelve) : walkGuard ⟨68,67,.west⟩ 1 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk184_1 : WalkBound ⟨68,67,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk184_1]; exact allowed)
  have checked := c6671 pattern guarded
  change d1104 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk184_2 (pattern : Twelve) : walkGuard ⟨68,67,.west⟩ 2 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk184_2 : WalkBound ⟨68,67,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk184_2]; exact allowed)
  have checked := c6711 pattern guarded
  change d1492 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk184_3 (pattern : Twelve) : walkGuard ⟨68,67,.west⟩ 3 pattern = decide (d1870 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk184_3 : WalkBound ⟨68,67,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1870 pattern = 1 := of_decide_eq_true (by rw [← guard_walk184_3]; exact allowed)
  have checked := c6733 pattern guarded
  change d1744 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk185_0 (pattern : Twelve) : walkGuard ⟨68,87,.southWest⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk185_0 : WalkBound ⟨68,87,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk185_0]; exact allowed)
  have checked := c6410 pattern guarded
  change d476 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk185_1 (pattern : Twelve) : walkGuard ⟨68,87,.southWest⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk185_1 : WalkBound ⟨68,87,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk185_1]; exact allowed)
  have checked := c6465 pattern guarded
  change d1104 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk185_2 (pattern : Twelve) : walkGuard ⟨68,87,.southWest⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk185_2 : WalkBound ⟨68,87,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk185_2]; exact allowed)
  have checked := c6504 pattern guarded
  change d1492 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk185_3 (pattern : Twelve) : walkGuard ⟨68,87,.southWest⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk185_3 : WalkBound ⟨68,87,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk185_3]; exact allowed)
  have checked := c6530 pattern guarded
  change d1744 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk186_0 (pattern : Twelve) : walkGuard ⟨68,47,.northWest⟩ 0 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk186_0 : WalkBound ⟨68,47,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk186_0]; exact allowed)
  have checked := c6832 pattern guarded
  change d476 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk186_1 (pattern : Twelve) : walkGuard ⟨68,47,.northWest⟩ 1 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk186_1 : WalkBound ⟨68,47,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk186_1]; exact allowed)
  have checked := c6898 pattern guarded
  change d1104 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk186_2 (pattern : Twelve) : walkGuard ⟨68,47,.northWest⟩ 2 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk186_2 : WalkBound ⟨68,47,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk186_2]; exact allowed)
  have checked := c6952 pattern guarded
  change d1492 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk186_3 (pattern : Twelve) : walkGuard ⟨68,47,.northWest⟩ 3 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk186_3 : WalkBound ⟨68,47,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk186_3]; exact allowed)
  have checked := c6978 pattern guarded
  change d1744 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk187_0 (pattern : Twelve) : walkGuard ⟨70,50,.north⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk187_0 : WalkBound ⟨70,50,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk187_0]; exact allowed)
  have checked := c7179 pattern guarded
  change d629 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk187_1 (pattern : Twelve) : walkGuard ⟨70,50,.north⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk187_1 : WalkBound ⟨70,50,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk187_1]; exact allowed)
  have checked := c7271 pattern guarded
  change d1182 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
