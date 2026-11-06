/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers08
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk315_0 (pattern : Ten) : walkGuard ⟨144,145,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk315_0 : WalkBound ⟨144,145,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk315_1 (pattern : Ten) : walkGuard ⟨144,145,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk315_1 : WalkBound ⟨144,145,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk315_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_0 (pattern : Ten) : walkGuard ⟨144,143,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk316_0 : WalkBound ⟨144,143,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk316_1 (pattern : Ten) : walkGuard ⟨144,143,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk316_1 : WalkBound ⟨144,143,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk316_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_0 (pattern : Ten) : walkGuard ⟨144,157,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk317_0 : WalkBound ⟨144,157,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk317_1 (pattern : Ten) : walkGuard ⟨144,157,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk317_1 : WalkBound ⟨144,157,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk317_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_0 (pattern : Ten) : walkGuard ⟨145,146,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk318_0 : WalkBound ⟨145,146,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk318_1 (pattern : Ten) : walkGuard ⟨145,146,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk318_1 : WalkBound ⟨145,146,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk318_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_0 (pattern : Ten) : walkGuard ⟨145,144,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk319_0 : WalkBound ⟨145,144,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk319_1 (pattern : Ten) : walkGuard ⟨145,144,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk319_1 : WalkBound ⟨145,144,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk319_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_0 (pattern : Ten) : walkGuard ⟨146,147,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk320_0 : WalkBound ⟨146,147,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk320_1 (pattern : Ten) : walkGuard ⟨146,147,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk320_1 : WalkBound ⟨146,147,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk320_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_0 (pattern : Ten) : walkGuard ⟨146,145,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk321_0 : WalkBound ⟨146,145,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk321_1 (pattern : Ten) : walkGuard ⟨146,145,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk321_1 : WalkBound ⟨146,145,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk321_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_0 (pattern : Ten) : walkGuard ⟨147,148,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk322_0 : WalkBound ⟨147,148,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk322_1 (pattern : Ten) : walkGuard ⟨147,148,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk322_1 : WalkBound ⟨147,148,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk322_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_0 (pattern : Ten) : walkGuard ⟨147,146,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk323_0 : WalkBound ⟨147,146,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk323_1 (pattern : Ten) : walkGuard ⟨147,146,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk323_1 : WalkBound ⟨147,146,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk323_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_0 (pattern : Ten) : walkGuard ⟨147,134,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk324_0 : WalkBound ⟨147,134,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk324_1 (pattern : Ten) : walkGuard ⟨147,134,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk324_1 : WalkBound ⟨147,134,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk324_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk325_0 (pattern : Ten) : walkGuard ⟨148,134,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk325_0 : WalkBound ⟨148,134,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk325_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk325_1 (pattern : Ten) : walkGuard ⟨148,134,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk325_1 : WalkBound ⟨148,134,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk325_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk326_0 (pattern : Ten) : walkGuard ⟨148,149,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk326_0 : WalkBound ⟨148,149,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk326_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk326_1 (pattern : Ten) : walkGuard ⟨148,149,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk326_1 : WalkBound ⟨148,149,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk326_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk327_0 (pattern : Ten) : walkGuard ⟨148,147,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk327_0 : WalkBound ⟨148,147,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk327_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk327_1 (pattern : Ten) : walkGuard ⟨148,147,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk327_1 : WalkBound ⟨148,147,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk327_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk328_0 (pattern : Ten) : walkGuard ⟨148,135,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk328_0 : WalkBound ⟨148,135,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk328_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk328_1 (pattern : Ten) : walkGuard ⟨148,135,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk328_1 : WalkBound ⟨148,135,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk328_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk329_0 (pattern : Ten) : walkGuard ⟨149,135,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk329_0 : WalkBound ⟨149,135,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk329_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk329_1 (pattern : Ten) : walkGuard ⟨149,135,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk329_1 : WalkBound ⟨149,135,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk329_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk330_0 (pattern : Ten) : walkGuard ⟨149,150,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk330_0 : WalkBound ⟨149,150,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk330_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk330_1 (pattern : Ten) : walkGuard ⟨149,150,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk330_1 : WalkBound ⟨149,150,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk330_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk331_0 (pattern : Ten) : walkGuard ⟨149,148,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk331_0 : WalkBound ⟨149,148,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk331_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk331_1 (pattern : Ten) : walkGuard ⟨149,148,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk331_1 : WalkBound ⟨149,148,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk331_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk332_0 (pattern : Ten) : walkGuard ⟨149,136,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk332_0 : WalkBound ⟨149,136,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk332_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk332_1 (pattern : Ten) : walkGuard ⟨149,136,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk332_1 : WalkBound ⟨149,136,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk332_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk333_0 (pattern : Ten) : walkGuard ⟨149,134,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk333_0 : WalkBound ⟨149,134,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk333_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk333_1 (pattern : Ten) : walkGuard ⟨149,134,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk333_1 : WalkBound ⟨149,134,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk333_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk334_0 (pattern : Ten) : walkGuard ⟨150,136,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk334_0 : WalkBound ⟨150,136,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk334_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk334_1 (pattern : Ten) : walkGuard ⟨150,136,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk334_1 : WalkBound ⟨150,136,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk334_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk335_0 (pattern : Ten) : walkGuard ⟨150,151,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk335_0 : WalkBound ⟨150,151,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk335_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk335_1 (pattern : Ten) : walkGuard ⟨150,151,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk335_1 : WalkBound ⟨150,151,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk335_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk336_0 (pattern : Ten) : walkGuard ⟨150,149,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk336_0 : WalkBound ⟨150,149,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk336_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk336_1 (pattern : Ten) : walkGuard ⟨150,149,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk336_1 : WalkBound ⟨150,149,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk336_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk337_0 (pattern : Ten) : walkGuard ⟨150,137,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk337_0 : WalkBound ⟨150,137,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk337_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk337_1 (pattern : Ten) : walkGuard ⟨150,137,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk337_1 : WalkBound ⟨150,137,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk337_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_0 (pattern : Ten) : walkGuard ⟨150,135,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk338_0 : WalkBound ⟨150,135,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk338_1 (pattern : Ten) : walkGuard ⟨150,135,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk338_1 : WalkBound ⟨150,135,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk338_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_0 (pattern : Ten) : walkGuard ⟨151,137,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk339_0 : WalkBound ⟨151,137,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk339_1 (pattern : Ten) : walkGuard ⟨151,137,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk339_1 : WalkBound ⟨151,137,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk339_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_0 (pattern : Ten) : walkGuard ⟨151,152,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk340_0 : WalkBound ⟨151,152,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk340_1 (pattern : Ten) : walkGuard ⟨151,152,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk340_1 : WalkBound ⟨151,152,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk340_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_0 (pattern : Ten) : walkGuard ⟨151,150,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk341_0 : WalkBound ⟨151,150,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk341_1 (pattern : Ten) : walkGuard ⟨151,150,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk341_1 : WalkBound ⟨151,150,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk341_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_0 (pattern : Ten) : walkGuard ⟨151,138,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk342_0 : WalkBound ⟨151,138,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk342_1 (pattern : Ten) : walkGuard ⟨151,138,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk342_1 : WalkBound ⟨151,138,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk342_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_0 (pattern : Ten) : walkGuard ⟨151,136,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk343_0 : WalkBound ⟨151,136,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk343_1 (pattern : Ten) : walkGuard ⟨151,136,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk343_1 : WalkBound ⟨151,136,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk343_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_0 (pattern : Ten) : walkGuard ⟨152,138,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk344_0 : WalkBound ⟨152,138,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk344_1 (pattern : Ten) : walkGuard ⟨152,138,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk344_1 : WalkBound ⟨152,138,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk344_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_0 (pattern : Ten) : walkGuard ⟨152,151,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk345_0 : WalkBound ⟨152,151,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk345_1 (pattern : Ten) : walkGuard ⟨152,151,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk345_1 : WalkBound ⟨152,151,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk345_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_0 (pattern : Ten) : walkGuard ⟨152,137,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk346_0 : WalkBound ⟨152,137,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk346_1 (pattern : Ten) : walkGuard ⟨152,137,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk346_1 : WalkBound ⟨152,137,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk346_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_0 (pattern : Ten) : walkGuard ⟨156,142,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk347_0 : WalkBound ⟨156,142,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk347_1 (pattern : Ten) : walkGuard ⟨156,142,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk347_1 : WalkBound ⟨156,142,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk347_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_0 (pattern : Ten) : walkGuard ⟨156,157,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk348_0 : WalkBound ⟨156,157,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk348_1 (pattern : Ten) : walkGuard ⟨156,157,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk348_1 : WalkBound ⟨156,157,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk348_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_0 (pattern : Ten) : walkGuard ⟨156,143,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk349_0 : WalkBound ⟨156,143,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk349_1 (pattern : Ten) : walkGuard ⟨156,143,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk349_1 : WalkBound ⟨156,143,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk349_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
