/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers03
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk140_0 (pattern : Ten) : walkGuard ⟨67,53,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk140_0 : WalkBound ⟨67,53,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk140_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk140_1 (pattern : Ten) : walkGuard ⟨67,53,.north⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk140_1 : WalkBound ⟨67,53,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk140_1]; exact allowed)
  have checked := c1249 pattern guarded
  change d340 pattern ≤ d300 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk141_0 (pattern : Ten) : walkGuard ⟨67,66,.west⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk141_0 : WalkBound ⟨67,66,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk141_0]; exact allowed)
  have checked := c1013 pattern guarded
  change d66 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk141_1 (pattern : Ten) : walkGuard ⟨67,66,.west⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk141_1 : WalkBound ⟨67,66,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk141_1]; exact allowed)
  have checked := c1263 pattern guarded
  change d340 pattern ≤ d331 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk142_0 (pattern : Ten) : walkGuard ⟨67,80,.southWest⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk142_0 : WalkBound ⟨67,80,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk142_0]; exact allowed)
  have checked := c1274 pattern guarded
  change d66 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk142_1 (pattern : Ten) : walkGuard ⟨67,80,.southWest⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk142_1 : WalkBound ⟨67,80,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk142_1]; exact allowed)
  have checked := c1285 pattern guarded
  change d340 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk143_0 (pattern : Ten) : walkGuard ⟨67,52,.northWest⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk143_0 : WalkBound ⟨67,52,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk143_0]; exact allowed)
  have checked := c333 pattern guarded
  change d66 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk143_1 (pattern : Ten) : walkGuard ⟨67,52,.northWest⟩ 1 pattern = decide (d405 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk143_1 : WalkBound ⟨67,52,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d405 pattern = 1 := of_decide_eq_true (by rw [← guard_walk143_1]; exact allowed)
  have checked := c1292 pattern guarded
  change d340 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk144_0 (pattern : Ten) : walkGuard ⟨80,66,.north⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk144_0 : WalkBound ⟨80,66,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk144_0]; exact allowed)
  have checked := c1308 pattern guarded
  change d170 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk144_1 (pattern : Ten) : walkGuard ⟨80,66,.north⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk144_1 : WalkBound ⟨80,66,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk144_1]; exact allowed)
  have checked := c1316 pattern guarded
  change d349 pattern ≤ d331 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk145_0 (pattern : Ten) : walkGuard ⟨80,94,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk145_0 : WalkBound ⟨80,94,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk145_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk145_1 (pattern : Ten) : walkGuard ⟨80,94,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk145_1 : WalkBound ⟨80,94,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk145_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk146_0 (pattern : Ten) : walkGuard ⟨80,67,.northEast⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk146_0 : WalkBound ⟨80,67,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk146_0]; exact allowed)
  have checked := c1328 pattern guarded
  change d170 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk146_1 (pattern : Ten) : walkGuard ⟨80,67,.northEast⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk146_1 : WalkBound ⟨80,67,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk146_1]; exact allowed)
  have checked := c1337 pattern guarded
  change d349 pattern ≤ d340 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk147_0 (pattern : Ten) : walkGuard ⟨80,95,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk147_0 : WalkBound ⟨80,95,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk147_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk147_1 (pattern : Ten) : walkGuard ⟨80,95,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk147_1 : WalkBound ⟨80,95,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk147_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk148_0 (pattern : Ten) : walkGuard ⟨80,93,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk148_0 : WalkBound ⟨80,93,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk148_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk148_1 (pattern : Ten) : walkGuard ⟨80,93,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk148_1 : WalkBound ⟨80,93,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk148_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk149_0 (pattern : Ten) : walkGuard ⟨85,86,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk149_0 : WalkBound ⟨85,86,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk149_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk149_1 (pattern : Ten) : walkGuard ⟨85,86,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk149_1 : WalkBound ⟨85,86,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk149_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk150_0 (pattern : Ten) : walkGuard ⟨85,99,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk150_0 : WalkBound ⟨85,99,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk150_1 (pattern : Ten) : walkGuard ⟨85,99,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk150_1 : WalkBound ⟨85,99,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk150_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_0 (pattern : Ten) : walkGuard ⟨85,100,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk151_0 : WalkBound ⟨85,100,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk151_1 (pattern : Ten) : walkGuard ⟨85,100,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk151_1 : WalkBound ⟨85,100,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk151_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_0 (pattern : Ten) : walkGuard ⟨86,87,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk152_0 : WalkBound ⟨86,87,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk152_1 (pattern : Ten) : walkGuard ⟨86,87,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk152_1 : WalkBound ⟨86,87,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk152_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_0 (pattern : Ten) : walkGuard ⟨86,100,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk153_0 : WalkBound ⟨86,100,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk153_1 (pattern : Ten) : walkGuard ⟨86,100,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk153_1 : WalkBound ⟨86,100,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk153_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_0 (pattern : Ten) : walkGuard ⟨86,85,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk154_0 : WalkBound ⟨86,85,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk154_1 (pattern : Ten) : walkGuard ⟨86,85,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk154_1 : WalkBound ⟨86,85,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk154_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_0 (pattern : Ten) : walkGuard ⟨86,99,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk155_0 : WalkBound ⟨86,99,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk155_1 (pattern : Ten) : walkGuard ⟨86,99,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk155_1 : WalkBound ⟨86,99,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk155_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_0 (pattern : Ten) : walkGuard ⟨87,88,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk156_0 : WalkBound ⟨87,88,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk156_1 (pattern : Ten) : walkGuard ⟨87,88,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk156_1 : WalkBound ⟨87,88,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk156_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_0 (pattern : Ten) : walkGuard ⟨87,86,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk157_0 : WalkBound ⟨87,86,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk157_1 (pattern : Ten) : walkGuard ⟨87,86,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk157_1 : WalkBound ⟨87,86,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk157_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_0 (pattern : Ten) : walkGuard ⟨87,100,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk158_0 : WalkBound ⟨87,100,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk158_1 (pattern : Ten) : walkGuard ⟨87,100,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk158_1 : WalkBound ⟨87,100,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk158_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_0 (pattern : Ten) : walkGuard ⟨88,89,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk159_0 : WalkBound ⟨88,89,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk159_1 (pattern : Ten) : walkGuard ⟨88,89,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk159_1 : WalkBound ⟨88,89,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk159_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_0 (pattern : Ten) : walkGuard ⟨88,87,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk160_0 : WalkBound ⟨88,87,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk160_1 (pattern : Ten) : walkGuard ⟨88,87,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk160_1 : WalkBound ⟨88,87,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk160_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_0 (pattern : Ten) : walkGuard ⟨89,90,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk161_0 : WalkBound ⟨89,90,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk161_1 (pattern : Ten) : walkGuard ⟨89,90,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk161_1 : WalkBound ⟨89,90,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk161_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk162_0 (pattern : Ten) : walkGuard ⟨89,88,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk162_0 : WalkBound ⟨89,88,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk162_1 (pattern : Ten) : walkGuard ⟨89,88,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk162_1 : WalkBound ⟨89,88,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk162_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_0 (pattern : Ten) : walkGuard ⟨90,89,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk163_0 : WalkBound ⟨90,89,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk163_1 (pattern : Ten) : walkGuard ⟨90,89,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk163_1 : WalkBound ⟨90,89,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk163_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_0 (pattern : Ten) : walkGuard ⟨92,93,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk164_0 : WalkBound ⟨92,93,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk164_1 (pattern : Ten) : walkGuard ⟨92,93,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk164_1 : WalkBound ⟨92,93,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk164_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_0 (pattern : Ten) : walkGuard ⟨92,106,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk165_0 : WalkBound ⟨92,106,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk165_1 (pattern : Ten) : walkGuard ⟨92,106,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk165_1 : WalkBound ⟨92,106,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk165_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_0 (pattern : Ten) : walkGuard ⟨92,107,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk166_0 : WalkBound ⟨92,107,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk166_1 (pattern : Ten) : walkGuard ⟨92,107,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk166_1 : WalkBound ⟨92,107,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk166_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_0 (pattern : Ten) : walkGuard ⟨93,94,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk167_0 : WalkBound ⟨93,94,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk167_1 (pattern : Ten) : walkGuard ⟨93,94,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk167_1 : WalkBound ⟨93,94,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk167_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_0 (pattern : Ten) : walkGuard ⟨93,107,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk168_0 : WalkBound ⟨93,107,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk168_1 (pattern : Ten) : walkGuard ⟨93,107,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk168_1 : WalkBound ⟨93,107,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk168_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_0 (pattern : Ten) : walkGuard ⟨93,92,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk169_0 : WalkBound ⟨93,92,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk169_1 (pattern : Ten) : walkGuard ⟨93,92,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk169_1 : WalkBound ⟨93,92,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk169_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_0 (pattern : Ten) : walkGuard ⟨93,80,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk170_0 : WalkBound ⟨93,80,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk170_1 (pattern : Ten) : walkGuard ⟨93,80,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk170_1 : WalkBound ⟨93,80,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk170_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_0 (pattern : Ten) : walkGuard ⟨93,108,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk171_0 : WalkBound ⟨93,108,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk171_1 (pattern : Ten) : walkGuard ⟨93,108,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk171_1 : WalkBound ⟨93,108,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk171_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_0 (pattern : Ten) : walkGuard ⟨93,106,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk172_0 : WalkBound ⟨93,106,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk172_1 (pattern : Ten) : walkGuard ⟨93,106,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk172_1 : WalkBound ⟨93,106,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk172_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_0 (pattern : Ten) : walkGuard ⟨94,80,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk173_0 : WalkBound ⟨94,80,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk173_1 (pattern : Ten) : walkGuard ⟨94,80,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk173_1 : WalkBound ⟨94,80,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk173_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_0 (pattern : Ten) : walkGuard ⟨94,95,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk174_0 : WalkBound ⟨94,95,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk174_1 (pattern : Ten) : walkGuard ⟨94,95,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk174_1 : WalkBound ⟨94,95,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk174_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
