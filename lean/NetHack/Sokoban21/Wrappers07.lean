/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers06
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk87_2 (pattern : Twelve) : walkGuard ⟨44,23,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk87_2 : WalkBound ⟨44,23,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk87_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk87_3 (pattern : Twelve) : walkGuard ⟨44,23,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk87_3 : WalkBound ⟨44,23,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk87_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_0 (pattern : Twelve) : walkGuard ⟨45,25,.north⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk88_0 : WalkBound ⟨45,25,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_1 (pattern : Twelve) : walkGuard ⟨45,25,.north⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk88_1 : WalkBound ⟨45,25,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_2 (pattern : Twelve) : walkGuard ⟨45,25,.north⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk88_2 : WalkBound ⟨45,25,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_3 (pattern : Twelve) : walkGuard ⟨45,25,.north⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk88_3 : WalkBound ⟨45,25,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_0 (pattern : Twelve) : walkGuard ⟨45,65,.south⟩ 0 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk89_0 : WalkBound ⟨45,65,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_0]; exact allowed)
  have checked := c709 pattern guarded
  change d234 pattern ≤ d351 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_1 (pattern : Twelve) : walkGuard ⟨45,65,.south⟩ 1 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk89_1 : WalkBound ⟨45,65,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_1]; exact allowed)
  have checked := c719 pattern guarded
  change d939 pattern ≤ d1017 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_2 (pattern : Twelve) : walkGuard ⟨45,65,.south⟩ 2 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk89_2 : WalkBound ⟨45,65,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_2]; exact allowed)
  have checked := c729 pattern guarded
  change d1379 pattern ≤ d1434 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_3 (pattern : Twelve) : walkGuard ⟨45,65,.south⟩ 3 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk89_3 : WalkBound ⟨45,65,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_3]; exact allowed)
  have checked := c731 pattern guarded
  change d1688 pattern ≤ d1714 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_0 (pattern : Twelve) : walkGuard ⟨45,44,.west⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk90_0 : WalkBound ⟨45,44,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_1 (pattern : Twelve) : walkGuard ⟨45,44,.west⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk90_1 : WalkBound ⟨45,44,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_2 (pattern : Twelve) : walkGuard ⟨45,44,.west⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk90_2 : WalkBound ⟨45,44,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_3 (pattern : Twelve) : walkGuard ⟨45,44,.west⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk90_3 : WalkBound ⟨45,44,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_0 (pattern : Twelve) : walkGuard ⟨45,26,.northEast⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk91_0 : WalkBound ⟨45,26,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_1 (pattern : Twelve) : walkGuard ⟨45,26,.northEast⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk91_1 : WalkBound ⟨45,26,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_2 (pattern : Twelve) : walkGuard ⟨45,26,.northEast⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk91_2 : WalkBound ⟨45,26,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_3 (pattern : Twelve) : walkGuard ⟨45,26,.northEast⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk91_3 : WalkBound ⟨45,26,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_0 (pattern : Twelve) : walkGuard ⟨45,66,.southEast⟩ 0 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk92_0 : WalkBound ⟨45,66,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_0]; exact allowed)
  have checked := c755 pattern guarded
  change d234 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_1 (pattern : Twelve) : walkGuard ⟨45,66,.southEast⟩ 1 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk92_1 : WalkBound ⟨45,66,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_1]; exact allowed)
  have checked := c779 pattern guarded
  change d939 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_2 (pattern : Twelve) : walkGuard ⟨45,66,.southEast⟩ 2 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk92_2 : WalkBound ⟨45,66,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_2]; exact allowed)
  have checked := c802 pattern guarded
  change d1379 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_3 (pattern : Twelve) : walkGuard ⟨45,66,.southEast⟩ 3 pattern = decide (d1846 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> cases j <;> rfl
theorem walk92_3 : WalkBound ⟨45,66,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1846 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_3]; exact allowed)
  have checked := c809 pattern guarded
  change d1688 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_0 (pattern : Twelve) : walkGuard ⟨45,64,.southWest⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk93_0 : WalkBound ⟨45,64,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_1 (pattern : Twelve) : walkGuard ⟨45,64,.southWest⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk93_1 : WalkBound ⟨45,64,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_2 (pattern : Twelve) : walkGuard ⟨45,64,.southWest⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk93_2 : WalkBound ⟨45,64,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_3 (pattern : Twelve) : walkGuard ⟨45,64,.southWest⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk93_3 : WalkBound ⟨45,64,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_0 (pattern : Twelve) : walkGuard ⟨45,24,.northWest⟩ 0 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk94_0 : WalkBound ⟨45,24,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_0]; exact allowed)
  have checked := c658 pattern guarded
  change d234 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_1 (pattern : Twelve) : walkGuard ⟨45,24,.northWest⟩ 1 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk94_1 : WalkBound ⟨45,24,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_1]; exact allowed)
  have checked := c677 pattern guarded
  change d939 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_2 (pattern : Twelve) : walkGuard ⟨45,24,.northWest⟩ 2 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk94_2 : WalkBound ⟨45,24,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_2]; exact allowed)
  have checked := c694 pattern guarded
  change d1379 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_3 (pattern : Twelve) : walkGuard ⟨45,24,.northWest⟩ 3 pattern = decide (d1835 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases d <;> rfl
theorem walk94_3 : WalkBound ⟨45,24,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1835 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_3]; exact allowed)
  have checked := c699 pattern guarded
  change d1688 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_0 (pattern : Twelve) : walkGuard ⟨47,27,.north⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk95_0 : WalkBound ⟨47,27,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_0]; exact allowed)
  have checked := c959 pattern guarded
  change d303 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_1 (pattern : Twelve) : walkGuard ⟨47,27,.north⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk95_1 : WalkBound ⟨47,27,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_1]; exact allowed)
  have checked := c1042 pattern guarded
  change d979 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_2 (pattern : Twelve) : walkGuard ⟨47,27,.north⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk95_2 : WalkBound ⟨47,27,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_2]; exact allowed)
  have checked := c1101 pattern guarded
  change d1411 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_3 (pattern : Twelve) : walkGuard ⟨47,27,.north⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> rfl
theorem walk95_3 : WalkBound ⟨47,27,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_3]; exact allowed)
  have checked := c1130 pattern guarded
  change d1704 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_0 (pattern : Twelve) : walkGuard ⟨47,48,.east⟩ 0 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk96_0 : WalkBound ⟨47,48,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_0]; exact allowed)
  have checked := c1185 pattern guarded
  change d303 pattern ≤ d344 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_1 (pattern : Twelve) : walkGuard ⟨47,48,.east⟩ 1 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk96_1 : WalkBound ⟨47,48,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_1]; exact allowed)
  have checked := c1225 pattern guarded
  change d979 pattern ≤ d1010 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_2 (pattern : Twelve) : walkGuard ⟨47,48,.east⟩ 2 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk96_2 : WalkBound ⟨47,48,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_2]; exact allowed)
  have checked := c1250 pattern guarded
  change d1411 pattern ≤ d1427 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_3 (pattern : Twelve) : walkGuard ⟨47,48,.east⟩ 3 pattern = decide (d1847 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk96_3 : WalkBound ⟨47,48,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1847 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_3]; exact allowed)
  have checked := c1261 pattern guarded
  change d1704 pattern ≤ d1713 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_0 (pattern : Twelve) : walkGuard ⟨47,67,.south⟩ 0 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk97_0 : WalkBound ⟨47,67,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_0]; exact allowed)
  have checked := c1395 pattern guarded
  change d303 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_1 (pattern : Twelve) : walkGuard ⟨47,67,.south⟩ 1 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk97_1 : WalkBound ⟨47,67,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_1]; exact allowed)
  have checked := c1468 pattern guarded
  change d979 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_2 (pattern : Twelve) : walkGuard ⟨47,67,.south⟩ 2 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk97_2 : WalkBound ⟨47,67,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_2]; exact allowed)
  have checked := c1522 pattern guarded
  change d1411 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_3 (pattern : Twelve) : walkGuard ⟨47,67,.south⟩ 3 pattern = decide (d1849 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem walk97_3 : WalkBound ⟨47,67,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1849 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_3]; exact allowed)
  have checked := c1557 pattern guarded
  change d1704 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_0 (pattern : Twelve) : walkGuard ⟨47,28,.northEast⟩ 0 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk98_0 : WalkBound ⟨47,28,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_0]; exact allowed)
  have checked := c959 pattern guarded
  change d303 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_1 (pattern : Twelve) : walkGuard ⟨47,28,.northEast⟩ 1 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk98_1 : WalkBound ⟨47,28,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_1]; exact allowed)
  have checked := c1042 pattern guarded
  change d979 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_2 (pattern : Twelve) : walkGuard ⟨47,28,.northEast⟩ 2 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk98_2 : WalkBound ⟨47,28,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_2]; exact allowed)
  have checked := c1101 pattern guarded
  change d1411 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_3 (pattern : Twelve) : walkGuard ⟨47,28,.northEast⟩ 3 pattern = decide (d1837 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases h <;> rfl
theorem walk98_3 : WalkBound ⟨47,28,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1837 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_3]; exact allowed)
  have checked := c1130 pattern guarded
  change d1704 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_0 (pattern : Twelve) : walkGuard ⟨47,68,.southEast⟩ 0 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk99_0 : WalkBound ⟨47,68,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_0]; exact allowed)
  have checked := c1667 pattern guarded
  change d303 pattern ≤ d476 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_1 (pattern : Twelve) : walkGuard ⟨47,68,.southEast⟩ 1 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk99_1 : WalkBound ⟨47,68,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_1]; exact allowed)
  have checked := c1738 pattern guarded
  change d979 pattern ≤ d1104 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_2 (pattern : Twelve) : walkGuard ⟨47,68,.southEast⟩ 2 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk99_2 : WalkBound ⟨47,68,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_2]; exact allowed)
  have checked := c1796 pattern guarded
  change d1411 pattern ≤ d1492 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_3 (pattern : Twelve) : walkGuard ⟨47,68,.southEast⟩ 3 pattern = decide (d1855 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> cases h <;> cases i <;> rfl
theorem walk99_3 : WalkBound ⟨47,68,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1855 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_3]; exact allowed)
  have checked := c1825 pattern guarded
  change d1704 pattern ≤ d1744 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
