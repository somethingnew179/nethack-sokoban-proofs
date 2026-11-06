/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers12
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk162_2 (pattern : Twelve) : walkGuard ⟨64,85,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk162_2 : WalkBound ⟨64,85,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk162_3 (pattern : Twelve) : walkGuard ⟨64,85,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk162_3 : WalkBound ⟨64,85,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_0 (pattern : Twelve) : walkGuard ⟨64,43,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk163_0 : WalkBound ⟨64,43,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_1 (pattern : Twelve) : walkGuard ⟨64,43,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk163_1 : WalkBound ⟨64,43,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_2 (pattern : Twelve) : walkGuard ⟨64,43,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk163_2 : WalkBound ⟨64,43,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_3 (pattern : Twelve) : walkGuard ⟨64,43,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk163_3 : WalkBound ⟨64,43,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_0 (pattern : Twelve) : walkGuard ⟨65,45,.north⟩ 0 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk164_0 : WalkBound ⟨65,45,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_0]; exact allowed)
  have checked := c4054 pattern guarded
  change d351 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_1 (pattern : Twelve) : walkGuard ⟨65,45,.north⟩ 1 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk164_1 : WalkBound ⟨65,45,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_1]; exact allowed)
  have checked := c4064 pattern guarded
  change d1017 pattern ≤ d939 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_2 (pattern : Twelve) : walkGuard ⟨65,45,.north⟩ 2 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk164_2 : WalkBound ⟨65,45,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_2]; exact allowed)
  have checked := c4074 pattern guarded
  change d1434 pattern ≤ d1379 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_3 (pattern : Twelve) : walkGuard ⟨65,45,.north⟩ 3 pattern = decide (d1842 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk164_3 : WalkBound ⟨65,45,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1842 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_3]; exact allowed)
  have checked := c4076 pattern guarded
  change d1714 pattern ≤ d1688 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_0 (pattern : Twelve) : walkGuard ⟨65,66,.east⟩ 0 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk165_0 : WalkBound ⟨65,66,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_0]; exact allowed)
  have checked := c4095 pattern guarded
  change d351 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_1 (pattern : Twelve) : walkGuard ⟨65,66,.east⟩ 1 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk165_1 : WalkBound ⟨65,66,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_1]; exact allowed)
  have checked := c4106 pattern guarded
  change d1017 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_2 (pattern : Twelve) : walkGuard ⟨65,66,.east⟩ 2 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk165_2 : WalkBound ⟨65,66,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_2]; exact allowed)
  have checked := c4115 pattern guarded
  change d1434 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_3 (pattern : Twelve) : walkGuard ⟨65,66,.east⟩ 3 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk165_3 : WalkBound ⟨65,66,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_3]; exact allowed)
  have checked := c4116 pattern guarded
  change d1714 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_0 (pattern : Twelve) : walkGuard ⟨65,85,.south⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk166_0 : WalkBound ⟨65,85,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_0]; exact allowed)
  have checked := c4126 pattern guarded
  change d351 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_1 (pattern : Twelve) : walkGuard ⟨65,85,.south⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk166_1 : WalkBound ⟨65,85,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_1]; exact allowed)
  have checked := c4136 pattern guarded
  change d1017 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_2 (pattern : Twelve) : walkGuard ⟨65,85,.south⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk166_2 : WalkBound ⟨65,85,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_2]; exact allowed)
  have checked := c4146 pattern guarded
  change d1434 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_3 (pattern : Twelve) : walkGuard ⟨65,85,.south⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk166_3 : WalkBound ⟨65,85,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_3]; exact allowed)
  have checked := c4148 pattern guarded
  change d1714 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_0 (pattern : Twelve) : walkGuard ⟨65,64,.west⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk167_0 : WalkBound ⟨65,64,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_0]; exact allowed)
  have checked := c4126 pattern guarded
  change d351 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_1 (pattern : Twelve) : walkGuard ⟨65,64,.west⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk167_1 : WalkBound ⟨65,64,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_1]; exact allowed)
  have checked := c4136 pattern guarded
  change d1017 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_2 (pattern : Twelve) : walkGuard ⟨65,64,.west⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk167_2 : WalkBound ⟨65,64,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_2]; exact allowed)
  have checked := c4146 pattern guarded
  change d1434 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_3 (pattern : Twelve) : walkGuard ⟨65,64,.west⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk167_3 : WalkBound ⟨65,64,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_3]; exact allowed)
  have checked := c4148 pattern guarded
  change d1714 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_0 (pattern : Twelve) : walkGuard ⟨65,84,.southWest⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk168_0 : WalkBound ⟨65,84,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_0]; exact allowed)
  have checked := c4126 pattern guarded
  change d351 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_1 (pattern : Twelve) : walkGuard ⟨65,84,.southWest⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk168_1 : WalkBound ⟨65,84,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_1]; exact allowed)
  have checked := c4136 pattern guarded
  change d1017 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_2 (pattern : Twelve) : walkGuard ⟨65,84,.southWest⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk168_2 : WalkBound ⟨65,84,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_2]; exact allowed)
  have checked := c4146 pattern guarded
  change d1434 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_3 (pattern : Twelve) : walkGuard ⟨65,84,.southWest⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> rfl
theorem walk168_3 : WalkBound ⟨65,84,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_3]; exact allowed)
  have checked := c4148 pattern guarded
  change d1714 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_0 (pattern : Twelve) : walkGuard ⟨65,44,.northWest⟩ 0 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk169_0 : WalkBound ⟨65,44,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_0]; exact allowed)
  have checked := c4126 pattern guarded
  change d351 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_1 (pattern : Twelve) : walkGuard ⟨65,44,.northWest⟩ 1 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk169_1 : WalkBound ⟨65,44,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_1]; exact allowed)
  have checked := c4136 pattern guarded
  change d1017 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_2 (pattern : Twelve) : walkGuard ⟨65,44,.northWest⟩ 2 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk169_2 : WalkBound ⟨65,44,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_2]; exact allowed)
  have checked := c4146 pattern guarded
  change d1434 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_3 (pattern : Twelve) : walkGuard ⟨65,44,.northWest⟩ 3 pattern = decide (d1841 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem walk169_3 : WalkBound ⟨65,44,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1841 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_3]; exact allowed)
  have checked := c4148 pattern guarded
  change d1714 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_0 (pattern : Twelve) : walkGuard ⟨66,67,.east⟩ 0 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk170_0 : WalkBound ⟨66,67,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_0]; exact allowed)
  have checked := c4214 pattern guarded
  change d365 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_1 (pattern : Twelve) : walkGuard ⟨66,67,.east⟩ 1 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk170_1 : WalkBound ⟨66,67,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_1]; exact allowed)
  have checked := c4264 pattern guarded
  change d1029 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_2 (pattern : Twelve) : walkGuard ⟨66,67,.east⟩ 2 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk170_2 : WalkBound ⟨66,67,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_2]; exact allowed)
  have checked := c4303 pattern guarded
  change d1443 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_3 (pattern : Twelve) : walkGuard ⟨66,67,.east⟩ 3 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk170_3 : WalkBound ⟨66,67,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_3]; exact allowed)
  have checked := c4318 pattern guarded
  change d1715 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_0 (pattern : Twelve) : walkGuard ⟨66,65,.west⟩ 0 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk171_0 : WalkBound ⟨66,65,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_0]; exact allowed)
  have checked := c4343 pattern guarded
  change d365 pattern ≤ d351 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_1 (pattern : Twelve) : walkGuard ⟨66,65,.west⟩ 1 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk171_1 : WalkBound ⟨66,65,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_1]; exact allowed)
  have checked := c4362 pattern guarded
  change d1029 pattern ≤ d1017 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_2 (pattern : Twelve) : walkGuard ⟨66,65,.west⟩ 2 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk171_2 : WalkBound ⟨66,65,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_2]; exact allowed)
  have checked := c4379 pattern guarded
  change d1443 pattern ≤ d1434 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_3 (pattern : Twelve) : walkGuard ⟨66,65,.west⟩ 3 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk171_3 : WalkBound ⟨66,65,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_3]; exact allowed)
  have checked := c4383 pattern guarded
  change d1715 pattern ≤ d1714 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_0 (pattern : Twelve) : walkGuard ⟨66,47,.northEast⟩ 0 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk172_0 : WalkBound ⟨66,47,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_0]; exact allowed)
  have checked := c4463 pattern guarded
  change d365 pattern ≤ d303 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_1 (pattern : Twelve) : walkGuard ⟨66,47,.northEast⟩ 1 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk172_1 : WalkBound ⟨66,47,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_1]; exact allowed)
  have checked := c4520 pattern guarded
  change d1029 pattern ≤ d979 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_2 (pattern : Twelve) : walkGuard ⟨66,47,.northEast⟩ 2 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk172_2 : WalkBound ⟨66,47,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_2]; exact allowed)
  have checked := c4564 pattern guarded
  change d1443 pattern ≤ d1411 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_3 (pattern : Twelve) : walkGuard ⟨66,47,.northEast⟩ 3 pattern = decide (d1857 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> cases j <;> rfl
theorem walk172_3 : WalkBound ⟨66,47,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1857 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_3]; exact allowed)
  have checked := c4585 pattern guarded
  change d1715 pattern ≤ d1704 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_0 (pattern : Twelve) : walkGuard ⟨66,87,.southEast⟩ 0 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk173_0 : WalkBound ⟨66,87,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_0]; exact allowed)
  have checked := c4685 pattern guarded
  change d365 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_1 (pattern : Twelve) : walkGuard ⟨66,87,.southEast⟩ 1 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk173_1 : WalkBound ⟨66,87,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_1]; exact allowed)
  have checked := c4773 pattern guarded
  change d1029 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_2 (pattern : Twelve) : walkGuard ⟨66,87,.southEast⟩ 2 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk173_2 : WalkBound ⟨66,87,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_2]; exact allowed)
  have checked := c4851 pattern guarded
  change d1443 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_3 (pattern : Twelve) : walkGuard ⟨66,87,.southEast⟩ 3 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk173_3 : WalkBound ⟨66,87,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_3]; exact allowed)
  have checked := c4880 pattern guarded
  change d1715 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_0 (pattern : Twelve) : walkGuard ⟨66,85,.southWest⟩ 0 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk174_0 : WalkBound ⟨66,85,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_0]; exact allowed)
  have checked := c4890 pattern guarded
  change d365 pattern ≤ d116 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_1 (pattern : Twelve) : walkGuard ⟨66,85,.southWest⟩ 1 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk174_1 : WalkBound ⟨66,85,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_1]; exact allowed)
  have checked := c4900 pattern guarded
  change d1029 pattern ≤ d871 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_2 (pattern : Twelve) : walkGuard ⟨66,85,.southWest⟩ 2 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk174_2 : WalkBound ⟨66,85,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_2]; exact allowed)
  have checked := c4909 pattern guarded
  change d1443 pattern ≤ d1323 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_3 (pattern : Twelve) : walkGuard ⟨66,85,.southWest⟩ 3 pattern = decide (d1868 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem walk174_3 : WalkBound ⟨66,85,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1868 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_3]; exact allowed)
  have checked := c4911 pattern guarded
  change d1715 pattern ≤ d1664 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
