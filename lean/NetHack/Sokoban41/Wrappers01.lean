/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers00
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk35_0 (pattern : Ten) : walkGuard ⟨30,29,.west⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk35_0 : WalkBound ⟨30,29,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk35_1 (pattern : Ten) : walkGuard ⟨30,29,.west⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk35_1 : WalkBound ⟨30,29,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk35_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_0 (pattern : Ten) : walkGuard ⟨30,17,.northEast⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk36_0 : WalkBound ⟨30,17,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk36_1 (pattern : Ten) : walkGuard ⟨30,17,.northEast⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk36_1 : WalkBound ⟨30,17,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk36_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk37_0 (pattern : Ten) : walkGuard ⟨30,45,.southEast⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk37_0 : WalkBound ⟨30,45,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk37_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk37_1 (pattern : Ten) : walkGuard ⟨30,45,.southEast⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk37_1 : WalkBound ⟨30,45,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk37_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk38_0 (pattern : Ten) : walkGuard ⟨30,43,.southWest⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk38_0 : WalkBound ⟨30,43,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk38_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk38_1 (pattern : Ten) : walkGuard ⟨30,43,.southWest⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk38_1 : WalkBound ⟨30,43,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk38_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk39_0 (pattern : Ten) : walkGuard ⟨30,15,.northWest⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk39_0 : WalkBound ⟨30,15,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk39_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk39_1 (pattern : Ten) : walkGuard ⟨30,15,.northWest⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk39_1 : WalkBound ⟨30,15,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk39_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk40_0 (pattern : Ten) : walkGuard ⟨31,17,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk40_0 : WalkBound ⟨31,17,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk40_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk40_1 (pattern : Ten) : walkGuard ⟨31,17,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk40_1 : WalkBound ⟨31,17,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk40_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk41_0 (pattern : Ten) : walkGuard ⟨31,32,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk41_0 : WalkBound ⟨31,32,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk41_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk41_1 (pattern : Ten) : walkGuard ⟨31,32,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk41_1 : WalkBound ⟨31,32,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk41_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk42_0 (pattern : Ten) : walkGuard ⟨31,45,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk42_0 : WalkBound ⟨31,45,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk42_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk42_1 (pattern : Ten) : walkGuard ⟨31,45,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk42_1 : WalkBound ⟨31,45,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk42_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk43_0 (pattern : Ten) : walkGuard ⟨31,30,.west⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk43_0 : WalkBound ⟨31,30,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk43_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk43_1 (pattern : Ten) : walkGuard ⟨31,30,.west⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk43_1 : WalkBound ⟨31,30,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk43_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk44_0 (pattern : Ten) : walkGuard ⟨31,18,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk44_0 : WalkBound ⟨31,18,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk44_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk44_1 (pattern : Ten) : walkGuard ⟨31,18,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk44_1 : WalkBound ⟨31,18,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk44_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk45_0 (pattern : Ten) : walkGuard ⟨31,46,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk45_0 : WalkBound ⟨31,46,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk45_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk45_1 (pattern : Ten) : walkGuard ⟨31,46,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk45_1 : WalkBound ⟨31,46,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk45_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk46_0 (pattern : Ten) : walkGuard ⟨31,44,.southWest⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk46_0 : WalkBound ⟨31,44,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk46_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk46_1 (pattern : Ten) : walkGuard ⟨31,44,.southWest⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk46_1 : WalkBound ⟨31,44,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk46_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk47_0 (pattern : Ten) : walkGuard ⟨31,16,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk47_0 : WalkBound ⟨31,16,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk47_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk47_1 (pattern : Ten) : walkGuard ⟨31,16,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk47_1 : WalkBound ⟨31,16,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk47_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk48_0 (pattern : Ten) : walkGuard ⟨32,18,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk48_0 : WalkBound ⟨32,18,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk48_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk48_1 (pattern : Ten) : walkGuard ⟨32,18,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk48_1 : WalkBound ⟨32,18,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk48_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk49_0 (pattern : Ten) : walkGuard ⟨32,46,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk49_0 : WalkBound ⟨32,46,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk49_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk49_1 (pattern : Ten) : walkGuard ⟨32,46,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk49_1 : WalkBound ⟨32,46,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk49_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk50_0 (pattern : Ten) : walkGuard ⟨32,31,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk50_0 : WalkBound ⟨32,31,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk50_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk50_1 (pattern : Ten) : walkGuard ⟨32,31,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk50_1 : WalkBound ⟨32,31,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk50_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk51_0 (pattern : Ten) : walkGuard ⟨32,47,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk51_0 : WalkBound ⟨32,47,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk51_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk51_1 (pattern : Ten) : walkGuard ⟨32,47,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk51_1 : WalkBound ⟨32,47,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk51_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk52_0 (pattern : Ten) : walkGuard ⟨32,45,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk52_0 : WalkBound ⟨32,45,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk52_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk52_1 (pattern : Ten) : walkGuard ⟨32,45,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk52_1 : WalkBound ⟨32,45,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk52_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk53_0 (pattern : Ten) : walkGuard ⟨32,17,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk53_0 : WalkBound ⟨32,17,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk53_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk53_1 (pattern : Ten) : walkGuard ⟨32,17,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk53_1 : WalkBound ⟨32,17,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk53_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk54_0 (pattern : Ten) : walkGuard ⟨37,23,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk54_0 : WalkBound ⟨37,23,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk54_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk54_1 (pattern : Ten) : walkGuard ⟨37,23,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk54_1 : WalkBound ⟨37,23,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk54_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk55_0 (pattern : Ten) : walkGuard ⟨37,38,.east⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk55_0 : WalkBound ⟨37,38,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk55_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk55_1 (pattern : Ten) : walkGuard ⟨37,38,.east⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk55_1 : WalkBound ⟨37,38,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk55_1]; exact allowed)
  have checked := c88 pattern guarded
  change d220 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk56_0 (pattern : Ten) : walkGuard ⟨37,51,.south⟩ 0 pattern = decide (d362 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem walk56_0 : WalkBound ⟨37,51,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d362 pattern = 1 := of_decide_eq_true (by rw [← guard_walk56_0]; exact allowed)
  have checked := c210 pattern guarded
  change d66 pattern ≤ d133 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk56_1 (pattern : Ten) : walkGuard ⟨37,51,.south⟩ 1 pattern = decide (d361 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem walk56_1 : WalkBound ⟨37,51,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d361 pattern = 1 := of_decide_eq_true (by rw [← guard_walk56_1]; exact allowed)
  have checked := c213 pattern guarded
  change d220 pattern ≤ d289 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk57_0 (pattern : Ten) : walkGuard ⟨37,24,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk57_0 : WalkBound ⟨37,24,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk57_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk57_1 (pattern : Ten) : walkGuard ⟨37,24,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk57_1 : WalkBound ⟨37,24,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk57_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk58_0 (pattern : Ten) : walkGuard ⟨37,52,.southEast⟩ 0 pattern = decide (d369 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk58_0 : WalkBound ⟨37,52,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d369 pattern = 1 := of_decide_eq_true (by rw [← guard_walk58_0]; exact allowed)
  have checked := c218 pattern guarded
  change d66 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk58_1 (pattern : Ten) : walkGuard ⟨37,52,.southEast⟩ 1 pattern = decide (d371 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk58_1 : WalkBound ⟨37,52,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d371 pattern = 1 := of_decide_eq_true (by rw [← guard_walk58_1]; exact allowed)
  have checked := c223 pattern guarded
  change d220 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk59_0 (pattern : Ten) : walkGuard ⟨37,50,.southWest⟩ 0 pattern = decide (d374 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk59_0 : WalkBound ⟨37,50,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d374 pattern = 1 := of_decide_eq_true (by rw [← guard_walk59_0]; exact allowed)
  have checked := c242 pattern guarded
  change d66 pattern ≤ d132 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk59_1 (pattern : Ten) : walkGuard ⟨37,50,.southWest⟩ 1 pattern = decide (d375 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk59_1 : WalkBound ⟨37,50,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d375 pattern = 1 := of_decide_eq_true (by rw [← guard_walk59_1]; exact allowed)
  have checked := c259 pattern guarded
  change d220 pattern ≤ d288 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk60_0 (pattern : Ten) : walkGuard ⟨38,24,.north⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk60_0 : WalkBound ⟨38,24,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk60_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk60_1 (pattern : Ten) : walkGuard ⟨38,24,.north⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk60_1 : WalkBound ⟨38,24,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk60_1]; exact allowed)
  have checked := c279 pattern guarded
  change d238 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk61_0 (pattern : Ten) : walkGuard ⟨38,39,.east⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk61_0 : WalkBound ⟨38,39,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk61_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk61_1 (pattern : Ten) : walkGuard ⟨38,39,.east⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk61_1 : WalkBound ⟨38,39,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk61_1]; exact allowed)
  have checked := c279 pattern guarded
  change d238 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk62_0 (pattern : Ten) : walkGuard ⟨38,52,.south⟩ 0 pattern = decide (d368 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk62_0 : WalkBound ⟨38,52,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d368 pattern = 1 := of_decide_eq_true (by rw [← guard_walk62_0]; exact allowed)
  have checked := c284 pattern guarded
  change d85 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk62_1 (pattern : Ten) : walkGuard ⟨38,52,.south⟩ 1 pattern = decide (d370 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk62_1 : WalkBound ⟨38,52,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d370 pattern = 1 := of_decide_eq_true (by rw [← guard_walk62_1]; exact allowed)
  have checked := c290 pattern guarded
  change d238 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_0 (pattern : Ten) : walkGuard ⟨38,37,.west⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk63_0 : WalkBound ⟨38,37,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk63_1 (pattern : Ten) : walkGuard ⟨38,37,.west⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk63_1 : WalkBound ⟨38,37,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk63_1]; exact allowed)
  have checked := c279 pattern guarded
  change d238 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_0 (pattern : Ten) : walkGuard ⟨38,25,.northEast⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk64_0 : WalkBound ⟨38,25,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk64_1 (pattern : Ten) : walkGuard ⟨38,25,.northEast⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk64_1 : WalkBound ⟨38,25,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk64_1]; exact allowed)
  have checked := c279 pattern guarded
  change d238 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_0 (pattern : Ten) : walkGuard ⟨38,53,.southEast⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk65_0 : WalkBound ⟨38,53,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk65_1 (pattern : Ten) : walkGuard ⟨38,53,.southEast⟩ 1 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk65_1 : WalkBound ⟨38,53,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk65_1]; exact allowed)
  have checked := c310 pattern guarded
  change d238 pattern ≤ d300 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_0 (pattern : Ten) : walkGuard ⟨38,51,.southWest⟩ 0 pattern = decide (d377 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk66_0 : WalkBound ⟨38,51,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d377 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_0]; exact allowed)
  have checked := c312 pattern guarded
  change d85 pattern ≤ d133 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk66_1 (pattern : Ten) : walkGuard ⟨38,51,.southWest⟩ 1 pattern = decide (d378 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk66_1 : WalkBound ⟨38,51,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d378 pattern = 1 := of_decide_eq_true (by rw [← guard_walk66_1]; exact allowed)
  have checked := c314 pattern guarded
  change d238 pattern ≤ d289 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_0 (pattern : Ten) : walkGuard ⟨38,23,.northWest⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk67_0 : WalkBound ⟨38,23,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_0]; exact allowed)
  have checked := c268 pattern guarded
  change d85 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk67_1 (pattern : Ten) : walkGuard ⟨38,23,.northWest⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk67_1 : WalkBound ⟨38,23,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk67_1]; exact allowed)
  have checked := c279 pattern guarded
  change d238 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_0 (pattern : Ten) : walkGuard ⟨39,25,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk68_0 : WalkBound ⟨39,25,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk68_1 (pattern : Ten) : walkGuard ⟨39,25,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk68_1 : WalkBound ⟨39,25,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk68_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_0 (pattern : Ten) : walkGuard ⟨39,53,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk69_0 : WalkBound ⟨39,53,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk69_1 (pattern : Ten) : walkGuard ⟨39,53,.south⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk69_1 : WalkBound ⟨39,53,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk69_1]; exact allowed)
  have checked := c330 pattern guarded
  change d220 pattern ≤ d300 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
