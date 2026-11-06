/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers19
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk250_0 (pattern : Twelve) : walkGuard ⟨87,68,.northEast⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk250_0 : WalkBound ⟨87,68,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_0]; exact allowed)
  have checked := c9174 pattern guarded
  change d156 pattern ≤ d476 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk250_1 (pattern : Twelve) : walkGuard ⟨87,68,.northEast⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk250_1 : WalkBound ⟨87,68,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_1]; exact allowed)
  have checked := c9226 pattern guarded
  change d907 pattern ≤ d1104 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk250_2 (pattern : Twelve) : walkGuard ⟨87,68,.northEast⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk250_2 : WalkBound ⟨87,68,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_2]; exact allowed)
  have checked := c9258 pattern guarded
  change d1354 pattern ≤ d1492 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk250_3 (pattern : Twelve) : walkGuard ⟨87,68,.northEast⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk250_3 : WalkBound ⟨87,68,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk250_3]; exact allowed)
  have checked := c9279 pattern guarded
  change d1678 pattern ≤ d1744 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_0 (pattern : Twelve) : walkGuard ⟨87,108,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk251_0 : WalkBound ⟨87,108,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_1 (pattern : Twelve) : walkGuard ⟨87,108,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk251_1 : WalkBound ⟨87,108,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_2 (pattern : Twelve) : walkGuard ⟨87,108,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk251_2 : WalkBound ⟨87,108,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk251_3 (pattern : Twelve) : walkGuard ⟨87,108,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk251_3 : WalkBound ⟨87,108,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk251_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_0 (pattern : Twelve) : walkGuard ⟨87,106,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk252_0 : WalkBound ⟨87,106,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_1 (pattern : Twelve) : walkGuard ⟨87,106,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk252_1 : WalkBound ⟨87,106,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_2 (pattern : Twelve) : walkGuard ⟨87,106,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk252_2 : WalkBound ⟨87,106,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk252_3 (pattern : Twelve) : walkGuard ⟨87,106,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk252_3 : WalkBound ⟨87,106,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk252_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_0 (pattern : Twelve) : walkGuard ⟨87,66,.northWest⟩ 0 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk253_0 : WalkBound ⟨87,66,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_0]; exact allowed)
  have checked := c9370 pattern guarded
  change d156 pattern ≤ d365 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_1 (pattern : Twelve) : walkGuard ⟨87,66,.northWest⟩ 1 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk253_1 : WalkBound ⟨87,66,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_1]; exact allowed)
  have checked := c9455 pattern guarded
  change d907 pattern ≤ d1029 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_2 (pattern : Twelve) : walkGuard ⟨87,66,.northWest⟩ 2 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk253_2 : WalkBound ⟨87,66,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_2]; exact allowed)
  have checked := c9530 pattern guarded
  change d1354 pattern ≤ d1443 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk253_3 (pattern : Twelve) : walkGuard ⟨87,66,.northWest⟩ 3 pattern = decide (d1869 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> cases j <;> rfl
theorem walk253_3 : WalkBound ⟨87,66,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1869 pattern = 1 := of_decide_eq_true (by rw [← guard_walk253_3]; exact allowed)
  have checked := c9557 pattern guarded
  change d1678 pattern ≤ d1715 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_0 (pattern : Twelve) : walkGuard ⟨88,68,.north⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk254_0 : WalkBound ⟨88,68,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_0]; exact allowed)
  have checked := c9174 pattern guarded
  change d156 pattern ≤ d476 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_1 (pattern : Twelve) : walkGuard ⟨88,68,.north⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk254_1 : WalkBound ⟨88,68,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_1]; exact allowed)
  have checked := c9226 pattern guarded
  change d907 pattern ≤ d1104 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_2 (pattern : Twelve) : walkGuard ⟨88,68,.north⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk254_2 : WalkBound ⟨88,68,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_2]; exact allowed)
  have checked := c9258 pattern guarded
  change d1354 pattern ≤ d1492 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk254_3 (pattern : Twelve) : walkGuard ⟨88,68,.north⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem walk254_3 : WalkBound ⟨88,68,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_walk254_3]; exact allowed)
  have checked := c9279 pattern guarded
  change d1678 pattern ≤ d1744 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_0 (pattern : Twelve) : walkGuard ⟨88,108,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk255_0 : WalkBound ⟨88,108,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_1 (pattern : Twelve) : walkGuard ⟨88,108,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk255_1 : WalkBound ⟨88,108,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_2 (pattern : Twelve) : walkGuard ⟨88,108,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk255_2 : WalkBound ⟨88,108,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk255_3 (pattern : Twelve) : walkGuard ⟨88,108,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk255_3 : WalkBound ⟨88,108,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk255_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_0 (pattern : Twelve) : walkGuard ⟨88,87,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk256_0 : WalkBound ⟨88,87,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_1 (pattern : Twelve) : walkGuard ⟨88,87,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk256_1 : WalkBound ⟨88,87,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_2 (pattern : Twelve) : walkGuard ⟨88,87,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk256_2 : WalkBound ⟨88,87,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk256_3 (pattern : Twelve) : walkGuard ⟨88,87,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk256_3 : WalkBound ⟨88,87,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk256_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_0 (pattern : Twelve) : walkGuard ⟨88,109,.southEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk257_0 : WalkBound ⟨88,109,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_1 (pattern : Twelve) : walkGuard ⟨88,109,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk257_1 : WalkBound ⟨88,109,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_2 (pattern : Twelve) : walkGuard ⟨88,109,.southEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk257_2 : WalkBound ⟨88,109,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk257_3 (pattern : Twelve) : walkGuard ⟨88,109,.southEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk257_3 : WalkBound ⟨88,109,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk257_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_0 (pattern : Twelve) : walkGuard ⟨88,107,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk258_0 : WalkBound ⟨88,107,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_1 (pattern : Twelve) : walkGuard ⟨88,107,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk258_1 : WalkBound ⟨88,107,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_2 (pattern : Twelve) : walkGuard ⟨88,107,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk258_2 : WalkBound ⟨88,107,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk258_3 (pattern : Twelve) : walkGuard ⟨88,107,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk258_3 : WalkBound ⟨88,107,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk258_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_0 (pattern : Twelve) : walkGuard ⟨88,67,.northWest⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk259_0 : WalkBound ⟨88,67,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_0]; exact allowed)
  have checked := c8970 pattern guarded
  change d156 pattern ≤ d424 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_1 (pattern : Twelve) : walkGuard ⟨88,67,.northWest⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk259_1 : WalkBound ⟨88,67,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_1]; exact allowed)
  have checked := c9030 pattern guarded
  change d907 pattern ≤ d1069 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_2 (pattern : Twelve) : walkGuard ⟨88,67,.northWest⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk259_2 : WalkBound ⟨88,67,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_2]; exact allowed)
  have checked := c9076 pattern guarded
  change d1354 pattern ≤ d1471 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk259_3 (pattern : Twelve) : walkGuard ⟨88,67,.northWest⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> rfl
theorem walk259_3 : WalkBound ⟨88,67,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_walk259_3]; exact allowed)
  have checked := c9103 pattern guarded
  change d1678 pattern ≤ d1729 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_0 (pattern : Twelve) : walkGuard ⟨90,70,.north⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk260_0 : WalkBound ⟨90,70,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_0]; exact allowed)
  have checked := c3039 pattern guarded
  change d156 pattern ≤ d629 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_1 (pattern : Twelve) : walkGuard ⟨90,70,.north⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk260_1 : WalkBound ⟨90,70,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_1]; exact allowed)
  have checked := c3134 pattern guarded
  change d907 pattern ≤ d1182 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_2 (pattern : Twelve) : walkGuard ⟨90,70,.north⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk260_2 : WalkBound ⟨90,70,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_2]; exact allowed)
  have checked := c3206 pattern guarded
  change d1354 pattern ≤ d1556 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk260_3 (pattern : Twelve) : walkGuard ⟨90,70,.north⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem walk260_3 : WalkBound ⟨90,70,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_walk260_3]; exact allowed)
  have checked := c3244 pattern guarded
  change d1678 pattern ≤ d1779 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_0 (pattern : Twelve) : walkGuard ⟨90,110,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk261_0 : WalkBound ⟨90,110,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_1 (pattern : Twelve) : walkGuard ⟨90,110,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk261_1 : WalkBound ⟨90,110,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_2 (pattern : Twelve) : walkGuard ⟨90,110,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk261_2 : WalkBound ⟨90,110,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk261_3 (pattern : Twelve) : walkGuard ⟨90,110,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk261_3 : WalkBound ⟨90,110,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk261_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk262_0 (pattern : Twelve) : walkGuard ⟨90,71,.northEast⟩ 0 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk262_0 : WalkBound ⟨90,71,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk262_0]; exact allowed)
  have checked := c3467 pattern guarded
  change d156 pattern ≤ d777 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk262_1 (pattern : Twelve) : walkGuard ⟨90,71,.northEast⟩ 1 pattern = decide (d1867 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem walk262_1 : WalkBound ⟨90,71,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1867 pattern = 1 := of_decide_eq_true (by rw [← guard_walk262_1]; exact allowed)
  have checked := c3562 pattern guarded
  change d907 pattern ≤ d1246 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
