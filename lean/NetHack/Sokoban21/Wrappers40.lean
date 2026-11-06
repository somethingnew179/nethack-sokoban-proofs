/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers39
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_walk500_0 (pattern : Twelve) : walkGuard ⟨146,166,.south⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk500_0 : WalkBound ⟨146,166,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk500_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk500_1 (pattern : Twelve) : walkGuard ⟨146,166,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk500_1 : WalkBound ⟨146,166,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk500_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk500_2 (pattern : Twelve) : walkGuard ⟨146,166,.south⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk500_2 : WalkBound ⟨146,166,.south⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk500_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk500_3 (pattern : Twelve) : walkGuard ⟨146,166,.south⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk500_3 : WalkBound ⟨146,166,.south⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk500_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk501_0 (pattern : Twelve) : walkGuard ⟨146,145,.west⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk501_0 : WalkBound ⟨146,145,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk501_0]; exact allowed)
  have checked := c9631 pattern guarded
  change d806 pattern ≤ d812 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk501_1 (pattern : Twelve) : walkGuard ⟨146,145,.west⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk501_1 : WalkBound ⟨146,145,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk501_1]; exact allowed)
  have checked := c9637 pattern guarded
  change d1267 pattern ≤ d1273 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk501_2 (pattern : Twelve) : walkGuard ⟨146,145,.west⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk501_2 : WalkBound ⟨146,145,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk501_2]; exact allowed)
  have checked := c9643 pattern guarded
  change d1636 pattern ≤ d1642 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk501_3 (pattern : Twelve) : walkGuard ⟨146,145,.west⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk501_3 : WalkBound ⟨146,145,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_walk501_3]; exact allowed)
  have checked := c9648 pattern guarded
  change d1827 pattern ≤ d1833 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk502_0 (pattern : Twelve) : walkGuard ⟨146,127,.northEast⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk502_0 : WalkBound ⟨146,127,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk502_0]; exact allowed)
  have checked := c9653 pattern guarded
  change d806 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk502_1 (pattern : Twelve) : walkGuard ⟨146,127,.northEast⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk502_1 : WalkBound ⟨146,127,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk502_1]; exact allowed)
  have checked := c9658 pattern guarded
  change d1267 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk502_2 (pattern : Twelve) : walkGuard ⟨146,127,.northEast⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk502_2 : WalkBound ⟨146,127,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk502_2]; exact allowed)
  have checked := c9663 pattern guarded
  change d1636 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk502_3 (pattern : Twelve) : walkGuard ⟨146,127,.northEast⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem walk502_3 : WalkBound ⟨146,127,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_walk502_3]; exact allowed)
  have checked := c9666 pattern guarded
  change d1827 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk503_0 (pattern : Twelve) : walkGuard ⟨146,165,.southWest⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk503_0 : WalkBound ⟨146,165,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk503_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk503_1 (pattern : Twelve) : walkGuard ⟨146,165,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk503_1 : WalkBound ⟨146,165,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk503_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk503_2 (pattern : Twelve) : walkGuard ⟨146,165,.southWest⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk503_2 : WalkBound ⟨146,165,.southWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk503_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk503_3 (pattern : Twelve) : walkGuard ⟨146,165,.southWest⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem walk503_3 : WalkBound ⟨146,165,.southWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk503_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk504_0 (pattern : Twelve) : walkGuard ⟨146,125,.northWest⟩ 0 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk504_0 : WalkBound ⟨146,125,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk504_0]; exact allowed)
  have checked := c9667 pattern guarded
  change d806 pattern ≤ d806 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk504_1 (pattern : Twelve) : walkGuard ⟨146,125,.northWest⟩ 1 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk504_1 : WalkBound ⟨146,125,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk504_1]; exact allowed)
  have checked := c9668 pattern guarded
  change d1267 pattern ≤ d1267 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk504_2 (pattern : Twelve) : walkGuard ⟨146,125,.northWest⟩ 2 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk504_2 : WalkBound ⟨146,125,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk504_2]; exact allowed)
  have checked := c9669 pattern guarded
  change d1636 pattern ≤ d1636 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk504_3 (pattern : Twelve) : walkGuard ⟨146,125,.northWest⟩ 3 pattern = decide (d1876 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> cases g <;> rfl
theorem walk504_3 : WalkBound ⟨146,125,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d1876 pattern = 1 := of_decide_eq_true (by rw [← guard_walk504_3]; exact allowed)
  have checked := c9670 pattern guarded
  change d1827 pattern ≤ d1827 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk505_0 (pattern : Twelve) : walkGuard ⟨148,149,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk505_0 : WalkBound ⟨148,149,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk505_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk505_1 (pattern : Twelve) : walkGuard ⟨148,149,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk505_1 : WalkBound ⟨148,149,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk505_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk505_2 (pattern : Twelve) : walkGuard ⟨148,149,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk505_2 : WalkBound ⟨148,149,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk505_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk505_3 (pattern : Twelve) : walkGuard ⟨148,149,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk505_3 : WalkBound ⟨148,149,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk505_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk506_0 (pattern : Twelve) : walkGuard ⟨148,129,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk506_0 : WalkBound ⟨148,129,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk506_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk506_1 (pattern : Twelve) : walkGuard ⟨148,129,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk506_1 : WalkBound ⟨148,129,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk506_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk506_2 (pattern : Twelve) : walkGuard ⟨148,129,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk506_2 : WalkBound ⟨148,129,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk506_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk506_3 (pattern : Twelve) : walkGuard ⟨148,129,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk506_3 : WalkBound ⟨148,129,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk506_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk507_0 (pattern : Twelve) : walkGuard ⟨148,127,.northWest⟩ 0 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk507_0 : WalkBound ⟨148,127,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk507_0]; exact allowed)
  have checked := c9729 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk507_1 (pattern : Twelve) : walkGuard ⟨148,127,.northWest⟩ 1 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk507_1 : WalkBound ⟨148,127,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk507_1]; exact allowed)
  have checked := c9730 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk507_2 (pattern : Twelve) : walkGuard ⟨148,127,.northWest⟩ 2 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk507_2 : WalkBound ⟨148,127,.northWest⟩ 2 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk507_2]; exact allowed)
  have checked := c9731 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk507_3 (pattern : Twelve) : walkGuard ⟨148,127,.northWest⟩ 3 pattern = decide (d0 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk507_3 : WalkBound ⟨148,127,.northWest⟩ 3 := by
  intro pattern allowed
  have guarded : d0 pattern = 1 := of_decide_eq_true (by rw [← guard_walk507_3]; exact allowed)
  have checked := c9732 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk508_0 (pattern : Twelve) : walkGuard ⟨149,129,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk508_0 : WalkBound ⟨149,129,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk508_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk508_1 (pattern : Twelve) : walkGuard ⟨149,129,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk508_1 : WalkBound ⟨149,129,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk508_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk508_2 (pattern : Twelve) : walkGuard ⟨149,129,.north⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk508_2 : WalkBound ⟨149,129,.north⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk508_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk508_3 (pattern : Twelve) : walkGuard ⟨149,129,.north⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk508_3 : WalkBound ⟨149,129,.north⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk508_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk509_0 (pattern : Twelve) : walkGuard ⟨149,150,.east⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk509_0 : WalkBound ⟨149,150,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk509_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk509_1 (pattern : Twelve) : walkGuard ⟨149,150,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk509_1 : WalkBound ⟨149,150,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk509_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk509_2 (pattern : Twelve) : walkGuard ⟨149,150,.east⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk509_2 : WalkBound ⟨149,150,.east⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk509_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk509_3 (pattern : Twelve) : walkGuard ⟨149,150,.east⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk509_3 : WalkBound ⟨149,150,.east⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk509_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk510_0 (pattern : Twelve) : walkGuard ⟨149,148,.west⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk510_0 : WalkBound ⟨149,148,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk510_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk510_1 (pattern : Twelve) : walkGuard ⟨149,148,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk510_1 : WalkBound ⟨149,148,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk510_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk510_2 (pattern : Twelve) : walkGuard ⟨149,148,.west⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk510_2 : WalkBound ⟨149,148,.west⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk510_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk510_3 (pattern : Twelve) : walkGuard ⟨149,148,.west⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk510_3 : WalkBound ⟨149,148,.west⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk510_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk511_0 (pattern : Twelve) : walkGuard ⟨149,130,.northEast⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk511_0 : WalkBound ⟨149,130,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk511_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk511_1 (pattern : Twelve) : walkGuard ⟨149,130,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk511_1 : WalkBound ⟨149,130,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk511_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk511_2 (pattern : Twelve) : walkGuard ⟨149,130,.northEast⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk511_2 : WalkBound ⟨149,130,.northEast⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk511_2]; exact allowed)
  have checked := c600 pattern guarded
  change d1354 pattern ≤ d1354 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk511_3 (pattern : Twelve) : walkGuard ⟨149,130,.northEast⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk511_3 : WalkBound ⟨149,130,.northEast⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk511_3]; exact allowed)
  have checked := c601 pattern guarded
  change d1678 pattern ≤ d1678 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk512_0 (pattern : Twelve) : walkGuard ⟨150,130,.north⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk512_0 : WalkBound ⟨150,130,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk512_0]; exact allowed)
  have checked := c598 pattern guarded
  change d156 pattern ≤ d156 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk512_1 (pattern : Twelve) : walkGuard ⟨150,130,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem walk512_1 : WalkBound ⟨150,130,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk512_1]; exact allowed)
  have checked := c599 pattern guarded
  change d907 pattern ≤ d907 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban21
