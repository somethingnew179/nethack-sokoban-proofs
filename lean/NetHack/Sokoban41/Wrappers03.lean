/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers02
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk105_0 (pattern : Ten) : walkGuard ⟨50,51,.east⟩ 0 pattern = decide (d374 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk105_0 : WalkBound ⟨50,51,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d374 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_0]; exact allowed)
  have checked := c798 pattern guarded
  change d132 pattern ≤ d133 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk105_1 (pattern : Ten) : walkGuard ⟨50,51,.east⟩ 1 pattern = decide (d375 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk105_1 : WalkBound ⟨50,51,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d375 pattern = 1 := of_decide_eq_true (by rw [← guard_walk105_1]; exact allowed)
  have checked := c812 pattern guarded
  change d288 pattern ≤ d289 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_0 (pattern : Ten) : walkGuard ⟨50,49,.west⟩ 0 pattern = decide (d390 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> rfl
theorem walk106_0 : WalkBound ⟨50,49,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d390 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_0]; exact allowed)
  have checked := c839 pattern guarded
  change d132 pattern ≤ d123 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk106_1 (pattern : Ten) : walkGuard ⟨50,49,.west⟩ 1 pattern = decide (d391 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> rfl
theorem walk106_1 : WalkBound ⟨50,49,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d391 pattern = 1 := of_decide_eq_true (by rw [← guard_walk106_1]; exact allowed)
  have checked := c861 pattern guarded
  change d288 pattern ≤ d279 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_0 (pattern : Ten) : walkGuard ⟨50,37,.northEast⟩ 0 pattern = decide (d374 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk107_0 : WalkBound ⟨50,37,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d374 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_0]; exact allowed)
  have checked := c863 pattern guarded
  change d132 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk107_1 (pattern : Ten) : walkGuard ⟨50,37,.northEast⟩ 1 pattern = decide (d375 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk107_1 : WalkBound ⟨50,37,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d375 pattern = 1 := of_decide_eq_true (by rw [← guard_walk107_1]; exact allowed)
  have checked := c865 pattern guarded
  change d288 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_0 (pattern : Ten) : walkGuard ⟨51,37,.north⟩ 0 pattern = decide (d362 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem walk108_0 : WalkBound ⟨51,37,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d362 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_0]; exact allowed)
  have checked := c867 pattern guarded
  change d133 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk108_1 (pattern : Ten) : walkGuard ⟨51,37,.north⟩ 1 pattern = decide (d361 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem walk108_1 : WalkBound ⟨51,37,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d361 pattern = 1 := of_decide_eq_true (by rw [← guard_walk108_1]; exact allowed)
  have checked := c869 pattern guarded
  change d289 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_0 (pattern : Ten) : walkGuard ⟨51,52,.east⟩ 0 pattern = decide (d392 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem walk109_0 : WalkBound ⟨51,52,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d392 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_0]; exact allowed)
  have checked := c871 pattern guarded
  change d133 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk109_1 (pattern : Ten) : walkGuard ⟨51,52,.east⟩ 1 pattern = decide (d393 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem walk109_1 : WalkBound ⟨51,52,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d393 pattern = 1 := of_decide_eq_true (by rw [← guard_walk109_1]; exact allowed)
  have checked := c873 pattern guarded
  change d289 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_0 (pattern : Ten) : walkGuard ⟨51,50,.west⟩ 0 pattern = decide (d374 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk110_0 : WalkBound ⟨51,50,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d374 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_0]; exact allowed)
  have checked := c875 pattern guarded
  change d133 pattern ≤ d132 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk110_1 (pattern : Ten) : walkGuard ⟨51,50,.west⟩ 1 pattern = decide (d375 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> rfl
theorem walk110_1 : WalkBound ⟨51,50,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d375 pattern = 1 := of_decide_eq_true (by rw [← guard_walk110_1]; exact allowed)
  have checked := c877 pattern guarded
  change d289 pattern ≤ d288 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_0 (pattern : Ten) : walkGuard ⟨51,38,.northEast⟩ 0 pattern = decide (d377 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk111_0 : WalkBound ⟨51,38,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d377 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_0]; exact allowed)
  have checked := c879 pattern guarded
  change d133 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk111_1 (pattern : Ten) : walkGuard ⟨51,38,.northEast⟩ 1 pattern = decide (d378 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk111_1 : WalkBound ⟨51,38,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d378 pattern = 1 := of_decide_eq_true (by rw [← guard_walk111_1]; exact allowed)
  have checked := c881 pattern guarded
  change d289 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk112_0 (pattern : Ten) : walkGuard ⟨51,66,.southEast⟩ 0 pattern = decide (d398 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases g <;> rfl
theorem walk112_0 : WalkBound ⟨51,66,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d398 pattern = 1 := of_decide_eq_true (by rw [← guard_walk112_0]; exact allowed)
  have checked := c889 pattern guarded
  change d133 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk112_1 (pattern : Ten) : walkGuard ⟨51,66,.southEast⟩ 1 pattern = decide (d401 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases g <;> rfl
theorem walk112_1 : WalkBound ⟨51,66,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d401 pattern = 1 := of_decide_eq_true (by rw [← guard_walk112_1]; exact allowed)
  have checked := c896 pattern guarded
  change d289 pattern ≤ d331 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk113_0 (pattern : Ten) : walkGuard ⟨52,38,.north⟩ 0 pattern = decide (d368 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk113_0 : WalkBound ⟨52,38,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d368 pattern = 1 := of_decide_eq_true (by rw [← guard_walk113_0]; exact allowed)
  have checked := c901 pattern guarded
  change d135 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk113_1 (pattern : Ten) : walkGuard ⟨52,38,.north⟩ 1 pattern = decide (d370 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk113_1 : WalkBound ⟨52,38,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d370 pattern = 1 := of_decide_eq_true (by rw [← guard_walk113_1]; exact allowed)
  have checked := c906 pattern guarded
  change d291 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk114_0 (pattern : Ten) : walkGuard ⟨52,53,.east⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> rfl
theorem walk114_0 : WalkBound ⟨52,53,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk114_0]; exact allowed)
  have checked := c911 pattern guarded
  change d135 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk114_1 (pattern : Ten) : walkGuard ⟨52,53,.east⟩ 1 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> rfl
theorem walk114_1 : WalkBound ⟨52,53,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk114_1]; exact allowed)
  have checked := c916 pattern guarded
  change d291 pattern ≤ d300 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk115_0 (pattern : Ten) : walkGuard ⟨52,66,.south⟩ 0 pattern = decide (d397 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk115_0 : WalkBound ⟨52,66,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d397 pattern = 1 := of_decide_eq_true (by rw [← guard_walk115_0]; exact allowed)
  have checked := c922 pattern guarded
  change d135 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk115_1 (pattern : Ten) : walkGuard ⟨52,66,.south⟩ 1 pattern = decide (d400 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk115_1 : WalkBound ⟨52,66,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d400 pattern = 1 := of_decide_eq_true (by rw [← guard_walk115_1]; exact allowed)
  have checked := c928 pattern guarded
  change d291 pattern ≤ d331 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk116_0 (pattern : Ten) : walkGuard ⟨52,51,.west⟩ 0 pattern = decide (d392 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem walk116_0 : WalkBound ⟨52,51,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d392 pattern = 1 := of_decide_eq_true (by rw [← guard_walk116_0]; exact allowed)
  have checked := c930 pattern guarded
  change d135 pattern ≤ d133 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk116_1 (pattern : Ten) : walkGuard ⟨52,51,.west⟩ 1 pattern = decide (d393 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem walk116_1 : WalkBound ⟨52,51,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d393 pattern = 1 := of_decide_eq_true (by rw [← guard_walk116_1]; exact allowed)
  have checked := c933 pattern guarded
  change d291 pattern ≤ d289 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk117_0 (pattern : Ten) : walkGuard ⟨52,39,.northEast⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk117_0 : WalkBound ⟨52,39,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk117_0]; exact allowed)
  have checked := c911 pattern guarded
  change d135 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk117_1 (pattern : Ten) : walkGuard ⟨52,39,.northEast⟩ 1 pattern = decide (d382 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk117_1 : WalkBound ⟨52,39,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d382 pattern = 1 := of_decide_eq_true (by rw [← guard_walk117_1]; exact allowed)
  have checked := c943 pattern guarded
  change d291 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk118_0 (pattern : Ten) : walkGuard ⟨52,67,.southEast⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk118_0 : WalkBound ⟨52,67,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk118_0]; exact allowed)
  have checked := c911 pattern guarded
  change d135 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk118_1 (pattern : Ten) : walkGuard ⟨52,67,.southEast⟩ 1 pattern = decide (d405 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk118_1 : WalkBound ⟨52,67,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d405 pattern = 1 := of_decide_eq_true (by rw [← guard_walk118_1]; exact allowed)
  have checked := c966 pattern guarded
  change d291 pattern ≤ d340 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk119_0 (pattern : Ten) : walkGuard ⟨52,37,.northWest⟩ 0 pattern = decide (d369 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk119_0 : WalkBound ⟨52,37,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d369 pattern = 1 := of_decide_eq_true (by rw [← guard_walk119_0]; exact allowed)
  have checked := c968 pattern guarded
  change d135 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk119_1 (pattern : Ten) : walkGuard ⟨52,37,.northWest⟩ 1 pattern = decide (d371 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases d <;> cases e <;> cases f <;> rfl
theorem walk119_1 : WalkBound ⟨52,37,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d371 pattern = 1 := of_decide_eq_true (by rw [← guard_walk119_1]; exact allowed)
  have checked := c970 pattern guarded
  change d291 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk120_0 (pattern : Ten) : walkGuard ⟨53,39,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk120_0 : WalkBound ⟨53,39,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk120_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk120_1 (pattern : Ten) : walkGuard ⟨53,39,.north⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk120_1 : WalkBound ⟨53,39,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk120_1]; exact allowed)
  have checked := c981 pattern guarded
  change d300 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk121_0 (pattern : Ten) : walkGuard ⟨53,67,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk121_0 : WalkBound ⟨53,67,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk121_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk121_1 (pattern : Ten) : walkGuard ⟨53,67,.south⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk121_1 : WalkBound ⟨53,67,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk121_1]; exact allowed)
  have checked := c995 pattern guarded
  change d300 pattern ≤ d340 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk122_0 (pattern : Ten) : walkGuard ⟨53,52,.west⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> rfl
theorem walk122_0 : WalkBound ⟨53,52,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk122_0]; exact allowed)
  have checked := c333 pattern guarded
  change d66 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk122_1 (pattern : Ten) : walkGuard ⟨53,52,.west⟩ 1 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> rfl
theorem walk122_1 : WalkBound ⟨53,52,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk122_1]; exact allowed)
  have checked := c998 pattern guarded
  change d300 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk123_0 (pattern : Ten) : walkGuard ⟨53,66,.southWest⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk123_0 : WalkBound ⟨53,66,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk123_0]; exact allowed)
  have checked := c1013 pattern guarded
  change d66 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk123_1 (pattern : Ten) : walkGuard ⟨53,66,.southWest⟩ 1 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk123_1 : WalkBound ⟨53,66,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk123_1]; exact allowed)
  have checked := c1029 pattern guarded
  change d300 pattern ≤ d331 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk124_0 (pattern : Ten) : walkGuard ⟨53,38,.northWest⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk124_0 : WalkBound ⟨53,38,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk124_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk124_1 (pattern : Ten) : walkGuard ⟨53,38,.northWest⟩ 1 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk124_1 : WalkBound ⟨53,38,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk124_1]; exact allowed)
  have checked := c1035 pattern guarded
  change d300 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk125_0 (pattern : Ten) : walkGuard ⟨57,43,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk125_0 : WalkBound ⟨57,43,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk125_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk125_1 (pattern : Ten) : walkGuard ⟨57,43,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk125_1 : WalkBound ⟨57,43,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk125_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk126_0 (pattern : Ten) : walkGuard ⟨57,58,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk126_0 : WalkBound ⟨57,58,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk126_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk126_1 (pattern : Ten) : walkGuard ⟨57,58,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk126_1 : WalkBound ⟨57,58,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk126_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk127_0 (pattern : Ten) : walkGuard ⟨57,44,.northEast⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk127_0 : WalkBound ⟨57,44,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk127_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk127_1 (pattern : Ten) : walkGuard ⟨57,44,.northEast⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk127_1 : WalkBound ⟨57,44,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk127_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk128_0 (pattern : Ten) : walkGuard ⟨58,44,.north⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk128_0 : WalkBound ⟨58,44,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk128_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk128_1 (pattern : Ten) : walkGuard ⟨58,44,.north⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk128_1 : WalkBound ⟨58,44,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk128_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk129_0 (pattern : Ten) : walkGuard ⟨58,57,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk129_0 : WalkBound ⟨58,57,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk129_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk129_1 (pattern : Ten) : walkGuard ⟨58,57,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk129_1 : WalkBound ⟨58,57,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk129_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk130_0 (pattern : Ten) : walkGuard ⟨58,45,.northEast⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk130_0 : WalkBound ⟨58,45,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk130_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk130_1 (pattern : Ten) : walkGuard ⟨58,45,.northEast⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk130_1 : WalkBound ⟨58,45,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk130_1]; exact allowed)
  have checked := c392 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk131_0 (pattern : Ten) : walkGuard ⟨58,43,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk131_0 : WalkBound ⟨58,43,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk131_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk131_1 (pattern : Ten) : walkGuard ⟨58,43,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk131_1 : WalkBound ⟨58,43,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk131_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk132_0 (pattern : Ten) : walkGuard ⟨62,48,.north⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk132_0 : WalkBound ⟨62,48,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk132_0]; exact allowed)
  have checked := c1048 pattern guarded
  change d149 pattern ≤ d107 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk132_1 (pattern : Ten) : walkGuard ⟨62,48,.north⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk132_1 : WalkBound ⟨62,48,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk132_1]; exact allowed)
  have checked := c1057 pattern guarded
  change d308 pattern ≤ d265 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk133_0 (pattern : Ten) : walkGuard ⟨62,49,.northEast⟩ 0 pattern = decide (d387 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk133_0 : WalkBound ⟨62,49,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d387 pattern = 1 := of_decide_eq_true (by rw [← guard_walk133_0]; exact allowed)
  have checked := c1086 pattern guarded
  change d149 pattern ≤ d123 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk133_1 (pattern : Ten) : walkGuard ⟨62,49,.northEast⟩ 1 pattern = decide (d388 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk133_1 : WalkBound ⟨62,49,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d388 pattern = 1 := of_decide_eq_true (by rw [← guard_walk133_1]; exact allowed)
  have checked := c1107 pattern guarded
  change d308 pattern ≤ d279 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk134_0 (pattern : Ten) : walkGuard ⟨62,47,.northWest⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk134_0 : WalkBound ⟨62,47,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk134_0]; exact allowed)
  have checked := c1121 pattern guarded
  change d149 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk134_1 (pattern : Ten) : walkGuard ⟨62,47,.northWest⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk134_1 : WalkBound ⟨62,47,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk134_1]; exact allowed)
  have checked := c1130 pattern guarded
  change d308 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk135_0 (pattern : Ten) : walkGuard ⟨66,52,.north⟩ 0 pattern = decide (d397 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk135_0 : WalkBound ⟨66,52,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d397 pattern = 1 := of_decide_eq_true (by rw [← guard_walk135_0]; exact allowed)
  have checked := c1138 pattern guarded
  change d156 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk135_1 (pattern : Ten) : walkGuard ⟨66,52,.north⟩ 1 pattern = decide (d400 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk135_1 : WalkBound ⟨66,52,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d400 pattern = 1 := of_decide_eq_true (by rw [← guard_walk135_1]; exact allowed)
  have checked := c1145 pattern guarded
  change d331 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk136_0 (pattern : Ten) : walkGuard ⟨66,67,.east⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk136_0 : WalkBound ⟨66,67,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk136_0]; exact allowed)
  have checked := c1158 pattern guarded
  change d156 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk136_1 (pattern : Ten) : walkGuard ⟨66,67,.east⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk136_1 : WalkBound ⟨66,67,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk136_1]; exact allowed)
  have checked := c1179 pattern guarded
  change d331 pattern ≤ d340 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk137_0 (pattern : Ten) : walkGuard ⟨66,80,.south⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk137_0 : WalkBound ⟨66,80,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk137_0]; exact allowed)
  have checked := c1195 pattern guarded
  change d156 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk137_1 (pattern : Ten) : walkGuard ⟨66,80,.south⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem walk137_1 : WalkBound ⟨66,80,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_walk137_1]; exact allowed)
  have checked := c1203 pattern guarded
  change d331 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk138_0 (pattern : Ten) : walkGuard ⟨66,53,.northEast⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk138_0 : WalkBound ⟨66,53,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk138_0]; exact allowed)
  have checked := c1158 pattern guarded
  change d156 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk138_1 (pattern : Ten) : walkGuard ⟨66,53,.northEast⟩ 1 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem walk138_1 : WalkBound ⟨66,53,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_walk138_1]; exact allowed)
  have checked := c1230 pattern guarded
  change d331 pattern ≤ d300 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk139_0 (pattern : Ten) : walkGuard ⟨66,51,.northWest⟩ 0 pattern = decide (d398 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases g <;> rfl
theorem walk139_0 : WalkBound ⟨66,51,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d398 pattern = 1 := of_decide_eq_true (by rw [← guard_walk139_0]; exact allowed)
  have checked := c1234 pattern guarded
  change d156 pattern ≤ d133 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk139_1 (pattern : Ten) : walkGuard ⟨66,51,.northWest⟩ 1 pattern = decide (d401 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases g <;> rfl
theorem walk139_1 : WalkBound ⟨66,51,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d401 pattern = 1 := of_decide_eq_true (by rw [← guard_walk139_1]; exact allowed)
  have checked := c1238 pattern guarded
  change d331 pattern ≤ d289 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
