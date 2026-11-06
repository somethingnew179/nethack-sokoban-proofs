/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers32
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk412_2 (pattern : Twelve) : walkGuard ⟨125,146,.southEast⟩ 2 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk412_2 : WalkBound ⟨125,146,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk412_2]; exact allowed)
  have checked := c9669 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk412_3 (pattern : Twelve) : walkGuard ⟨125,146,.southEast⟩ 3 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk412_3 : WalkBound ⟨125,146,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk412_3]; exact allowed)
  have checked := c9670 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk413_0 (pattern : Twelve) : walkGuard ⟨126,106,.north⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk413_0 : WalkBound ⟨126,106,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk413_0]; exact allowed)
  have checked := c9675 pattern guarded
  change d809 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk413_1 (pattern : Twelve) : walkGuard ⟨126,106,.north⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk413_1 : WalkBound ⟨126,106,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk413_1]; exact allowed)
  have checked := c9680 pattern guarded
  change d1270 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk413_2 (pattern : Twelve) : walkGuard ⟨126,106,.north⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk413_2 : WalkBound ⟨126,106,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk413_2]; exact allowed)
  have checked := c9685 pattern guarded
  change d1639 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk413_3 (pattern : Twelve) : walkGuard ⟨126,106,.north⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk413_3 : WalkBound ⟨126,106,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk413_3]; exact allowed)
  have checked := c9690 pattern guarded
  change d1830 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk414_0 (pattern : Twelve) : walkGuard ⟨126,127,.east⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk414_0 : WalkBound ⟨126,127,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk414_0]; exact allowed)
  have checked := c9675 pattern guarded
  change d809 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk414_1 (pattern : Twelve) : walkGuard ⟨126,127,.east⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk414_1 : WalkBound ⟨126,127,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk414_1]; exact allowed)
  have checked := c9680 pattern guarded
  change d1270 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk414_2 (pattern : Twelve) : walkGuard ⟨126,127,.east⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk414_2 : WalkBound ⟨126,127,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk414_2]; exact allowed)
  have checked := c9685 pattern guarded
  change d1639 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk414_3 (pattern : Twelve) : walkGuard ⟨126,127,.east⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk414_3 : WalkBound ⟨126,127,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk414_3]; exact allowed)
  have checked := c9690 pattern guarded
  change d1830 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk415_0 (pattern : Twelve) : walkGuard ⟨126,146,.south⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk415_0 : WalkBound ⟨126,146,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk415_0]; exact allowed)
  have checked := c9695 pattern guarded
  change d809 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk415_1 (pattern : Twelve) : walkGuard ⟨126,146,.south⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk415_1 : WalkBound ⟨126,146,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk415_1]; exact allowed)
  have checked := c9700 pattern guarded
  change d1270 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk415_2 (pattern : Twelve) : walkGuard ⟨126,146,.south⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk415_2 : WalkBound ⟨126,146,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk415_2]; exact allowed)
  have checked := c9705 pattern guarded
  change d1639 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk415_3 (pattern : Twelve) : walkGuard ⟨126,146,.south⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk415_3 : WalkBound ⟨126,146,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk415_3]; exact allowed)
  have checked := c9708 pattern guarded
  change d1830 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk416_0 (pattern : Twelve) : walkGuard ⟨126,125,.west⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk416_0 : WalkBound ⟨126,125,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk416_0]; exact allowed)
  have checked := c9695 pattern guarded
  change d809 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk416_1 (pattern : Twelve) : walkGuard ⟨126,125,.west⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk416_1 : WalkBound ⟨126,125,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk416_1]; exact allowed)
  have checked := c9700 pattern guarded
  change d1270 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk416_2 (pattern : Twelve) : walkGuard ⟨126,125,.west⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk416_2 : WalkBound ⟨126,125,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk416_2]; exact allowed)
  have checked := c9705 pattern guarded
  change d1639 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk416_3 (pattern : Twelve) : walkGuard ⟨126,125,.west⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk416_3 : WalkBound ⟨126,125,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk416_3]; exact allowed)
  have checked := c9708 pattern guarded
  change d1830 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk417_0 (pattern : Twelve) : walkGuard ⟨126,107,.northEast⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk417_0 : WalkBound ⟨126,107,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk417_0]; exact allowed)
  have checked := c9675 pattern guarded
  change d809 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk417_1 (pattern : Twelve) : walkGuard ⟨126,107,.northEast⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk417_1 : WalkBound ⟨126,107,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk417_1]; exact allowed)
  have checked := c9680 pattern guarded
  change d1270 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk417_2 (pattern : Twelve) : walkGuard ⟨126,107,.northEast⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk417_2 : WalkBound ⟨126,107,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk417_2]; exact allowed)
  have checked := c9685 pattern guarded
  change d1639 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk417_3 (pattern : Twelve) : walkGuard ⟨126,107,.northEast⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk417_3 : WalkBound ⟨126,107,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk417_3]; exact allowed)
  have checked := c9690 pattern guarded
  change d1830 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk418_0 (pattern : Twelve) : walkGuard ⟨126,145,.southWest⟩ 0 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk418_0 : WalkBound ⟨126,145,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk418_0]; exact allowed)
  have checked := c9713 pattern guarded
  change d809 pattern ≤ d812 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk418_1 (pattern : Twelve) : walkGuard ⟨126,145,.southWest⟩ 1 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk418_1 : WalkBound ⟨126,145,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk418_1]; exact allowed)
  have checked := c9718 pattern guarded
  change d1270 pattern ≤ d1273 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk418_2 (pattern : Twelve) : walkGuard ⟨126,145,.southWest⟩ 2 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk418_2 : WalkBound ⟨126,145,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk418_2]; exact allowed)
  have checked := c9723 pattern guarded
  change d1639 pattern ≤ d1642 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk418_3 (pattern : Twelve) : walkGuard ⟨126,145,.southWest⟩ 3 pattern = decide (d1877 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk418_3 : WalkBound ⟨126,145,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1877 pattern = 1 := of_decide_eq_true (by rw [← guard_walk418_3]; exact allowed)
  have checked := c9728 pattern guarded
  change d1830 pattern ≤ d1833 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk419_0 (pattern : Twelve) : walkGuard ⟨127,107,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk419_0 : WalkBound ⟨127,107,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk419_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk419_1 (pattern : Twelve) : walkGuard ⟨127,107,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk419_1 : WalkBound ⟨127,107,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk419_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk419_2 (pattern : Twelve) : walkGuard ⟨127,107,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk419_2 : WalkBound ⟨127,107,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk419_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk419_3 (pattern : Twelve) : walkGuard ⟨127,107,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk419_3 : WalkBound ⟨127,107,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk419_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk420_0 (pattern : Twelve) : walkGuard ⟨127,126,.west⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk420_0 : WalkBound ⟨127,126,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk420_0]; exact allowed)
  have checked := c9564 pattern guarded
  change d156 pattern ≤ d809 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk420_1 (pattern : Twelve) : walkGuard ⟨127,126,.west⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk420_1 : WalkBound ⟨127,126,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk420_1]; exact allowed)
  have checked := c9571 pattern guarded
  change d907 pattern ≤ d1270 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk420_2 (pattern : Twelve) : walkGuard ⟨127,126,.west⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk420_2 : WalkBound ⟨127,126,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk420_2]; exact allowed)
  have checked := c9578 pattern guarded
  change d1354 pattern ≤ d1639 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk420_3 (pattern : Twelve) : walkGuard ⟨127,126,.west⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk420_3 : WalkBound ⟨127,126,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk420_3]; exact allowed)
  have checked := c9584 pattern guarded
  change d1678 pattern ≤ d1830 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk421_0 (pattern : Twelve) : walkGuard ⟨127,108,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk421_0 : WalkBound ⟨127,108,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk421_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk421_1 (pattern : Twelve) : walkGuard ⟨127,108,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk421_1 : WalkBound ⟨127,108,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk421_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk421_2 (pattern : Twelve) : walkGuard ⟨127,108,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk421_2 : WalkBound ⟨127,108,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk421_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk421_3 (pattern : Twelve) : walkGuard ⟨127,108,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk421_3 : WalkBound ⟨127,108,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk421_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk422_0 (pattern : Twelve) : walkGuard ⟨127,148,.southEast⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk422_0 : WalkBound ⟨127,148,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk422_0]; exact allowed)
  have checked := c9729 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk422_1 (pattern : Twelve) : walkGuard ⟨127,148,.southEast⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk422_1 : WalkBound ⟨127,148,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk422_1]; exact allowed)
  have checked := c9730 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk422_2 (pattern : Twelve) : walkGuard ⟨127,148,.southEast⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk422_2 : WalkBound ⟨127,148,.southEast⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk422_2]; exact allowed)
  have checked := c9731 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk422_3 (pattern : Twelve) : walkGuard ⟨127,148,.southEast⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk422_3 : WalkBound ⟨127,148,.southEast⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk422_3]; exact allowed)
  have checked := c9732 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk423_0 (pattern : Twelve) : walkGuard ⟨127,146,.southWest⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk423_0 : WalkBound ⟨127,146,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk423_0]; exact allowed)
  have checked := c9589 pattern guarded
  change d156 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk423_1 (pattern : Twelve) : walkGuard ⟨127,146,.southWest⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk423_1 : WalkBound ⟨127,146,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk423_1]; exact allowed)
  have checked := c9594 pattern guarded
  change d907 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk423_2 (pattern : Twelve) : walkGuard ⟨127,146,.southWest⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk423_2 : WalkBound ⟨127,146,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk423_2]; exact allowed)
  have checked := c9599 pattern guarded
  change d1354 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk423_3 (pattern : Twelve) : walkGuard ⟨127,146,.southWest⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk423_3 : WalkBound ⟨127,146,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk423_3]; exact allowed)
  have checked := c9603 pattern guarded
  change d1678 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk424_0 (pattern : Twelve) : walkGuard ⟨127,106,.northWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk424_0 : WalkBound ⟨127,106,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk424_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk424_1 (pattern : Twelve) : walkGuard ⟨127,106,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk424_1 : WalkBound ⟨127,106,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk424_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk424_2 (pattern : Twelve) : walkGuard ⟨127,106,.northWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk424_2 : WalkBound ⟨127,106,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk424_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk424_3 (pattern : Twelve) : walkGuard ⟨127,106,.northWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk424_3 : WalkBound ⟨127,106,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk424_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
