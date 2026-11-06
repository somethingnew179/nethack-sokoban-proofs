/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Comparisons35
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk0_0 (pattern : Ten) : walkGuard ⟨15,16,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk0_0 : WalkBound ⟨15,16,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk0_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk0_1 (pattern : Ten) : walkGuard ⟨15,16,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk0_1 : WalkBound ⟨15,16,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk0_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk1_0 (pattern : Ten) : walkGuard ⟨15,29,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk1_0 : WalkBound ⟨15,29,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk1_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk1_1 (pattern : Ten) : walkGuard ⟨15,29,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk1_1 : WalkBound ⟨15,29,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk1_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk2_0 (pattern : Ten) : walkGuard ⟨15,30,.southEast⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk2_0 : WalkBound ⟨15,30,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk2_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk2_1 (pattern : Ten) : walkGuard ⟨15,30,.southEast⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk2_1 : WalkBound ⟨15,30,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk2_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk3_0 (pattern : Ten) : walkGuard ⟨16,17,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk3_0 : WalkBound ⟨16,17,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk3_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk3_1 (pattern : Ten) : walkGuard ⟨16,17,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk3_1 : WalkBound ⟨16,17,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk3_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk4_0 (pattern : Ten) : walkGuard ⟨16,30,.south⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk4_0 : WalkBound ⟨16,30,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk4_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk4_1 (pattern : Ten) : walkGuard ⟨16,30,.south⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk4_1 : WalkBound ⟨16,30,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk4_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk5_0 (pattern : Ten) : walkGuard ⟨16,15,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk5_0 : WalkBound ⟨16,15,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk5_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk5_1 (pattern : Ten) : walkGuard ⟨16,15,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk5_1 : WalkBound ⟨16,15,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk5_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk6_0 (pattern : Ten) : walkGuard ⟨16,31,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk6_0 : WalkBound ⟨16,31,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk6_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk6_1 (pattern : Ten) : walkGuard ⟨16,31,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk6_1 : WalkBound ⟨16,31,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk6_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk7_0 (pattern : Ten) : walkGuard ⟨16,29,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk7_0 : WalkBound ⟨16,29,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk7_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk7_1 (pattern : Ten) : walkGuard ⟨16,29,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk7_1 : WalkBound ⟨16,29,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk7_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk8_0 (pattern : Ten) : walkGuard ⟨17,18,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk8_0 : WalkBound ⟨17,18,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk8_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk8_1 (pattern : Ten) : walkGuard ⟨17,18,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk8_1 : WalkBound ⟨17,18,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk8_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk9_0 (pattern : Ten) : walkGuard ⟨17,31,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk9_0 : WalkBound ⟨17,31,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk9_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk9_1 (pattern : Ten) : walkGuard ⟨17,31,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk9_1 : WalkBound ⟨17,31,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk9_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk10_0 (pattern : Ten) : walkGuard ⟨17,16,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk10_0 : WalkBound ⟨17,16,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk10_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk10_1 (pattern : Ten) : walkGuard ⟨17,16,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk10_1 : WalkBound ⟨17,16,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk10_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk11_0 (pattern : Ten) : walkGuard ⟨17,32,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk11_0 : WalkBound ⟨17,32,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk11_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk11_1 (pattern : Ten) : walkGuard ⟨17,32,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk11_1 : WalkBound ⟨17,32,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk11_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk12_0 (pattern : Ten) : walkGuard ⟨17,30,.southWest⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk12_0 : WalkBound ⟨17,30,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk12_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk12_1 (pattern : Ten) : walkGuard ⟨17,30,.southWest⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk12_1 : WalkBound ⟨17,30,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk12_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_0 (pattern : Ten) : walkGuard ⟨18,32,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk13_0 : WalkBound ⟨18,32,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk13_1 (pattern : Ten) : walkGuard ⟨18,32,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk13_1 : WalkBound ⟨18,32,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk13_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_0 (pattern : Ten) : walkGuard ⟨18,17,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk14_0 : WalkBound ⟨18,17,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk14_1 (pattern : Ten) : walkGuard ⟨18,17,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk14_1 : WalkBound ⟨18,17,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk14_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_0 (pattern : Ten) : walkGuard ⟨18,31,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk15_0 : WalkBound ⟨18,31,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk15_1 (pattern : Ten) : walkGuard ⟨18,31,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk15_1 : WalkBound ⟨18,31,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk15_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_0 (pattern : Ten) : walkGuard ⟨23,24,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk16_0 : WalkBound ⟨23,24,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk16_1 (pattern : Ten) : walkGuard ⟨23,24,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk16_1 : WalkBound ⟨23,24,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk16_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_0 (pattern : Ten) : walkGuard ⟨23,37,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk17_0 : WalkBound ⟨23,37,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk17_1 (pattern : Ten) : walkGuard ⟨23,37,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk17_1 : WalkBound ⟨23,37,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk17_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_0 (pattern : Ten) : walkGuard ⟨23,38,.southEast⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk18_0 : WalkBound ⟨23,38,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk18_1 (pattern : Ten) : walkGuard ⟨23,38,.southEast⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk18_1 : WalkBound ⟨23,38,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk18_1]; exact allowed)
  have checked := c88 pattern guarded
  change d220 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_0 (pattern : Ten) : walkGuard ⟨24,25,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk19_0 : WalkBound ⟨24,25,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk19_1 (pattern : Ten) : walkGuard ⟨24,25,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk19_1 : WalkBound ⟨24,25,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk19_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_0 (pattern : Ten) : walkGuard ⟨24,38,.south⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk20_0 : WalkBound ⟨24,38,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk20_1 (pattern : Ten) : walkGuard ⟨24,38,.south⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk20_1 : WalkBound ⟨24,38,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk20_1]; exact allowed)
  have checked := c88 pattern guarded
  change d220 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_0 (pattern : Ten) : walkGuard ⟨24,23,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk21_0 : WalkBound ⟨24,23,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk21_1 (pattern : Ten) : walkGuard ⟨24,23,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk21_1 : WalkBound ⟨24,23,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk21_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_0 (pattern : Ten) : walkGuard ⟨24,39,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk22_0 : WalkBound ⟨24,39,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk22_1 (pattern : Ten) : walkGuard ⟨24,39,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk22_1 : WalkBound ⟨24,39,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk22_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_0 (pattern : Ten) : walkGuard ⟨24,37,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk23_0 : WalkBound ⟨24,37,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk23_1 (pattern : Ten) : walkGuard ⟨24,37,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk23_1 : WalkBound ⟨24,37,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk23_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_0 (pattern : Ten) : walkGuard ⟨25,39,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk24_0 : WalkBound ⟨25,39,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk24_1 (pattern : Ten) : walkGuard ⟨25,39,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk24_1 : WalkBound ⟨25,39,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk24_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk25_0 (pattern : Ten) : walkGuard ⟨25,24,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk25_0 : WalkBound ⟨25,24,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk25_1 (pattern : Ten) : walkGuard ⟨25,24,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk25_1 : WalkBound ⟨25,24,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk25_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_0 (pattern : Ten) : walkGuard ⟨25,38,.southWest⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk26_0 : WalkBound ⟨25,38,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk26_1 (pattern : Ten) : walkGuard ⟨25,38,.southWest⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk26_1 : WalkBound ⟨25,38,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk26_1]; exact allowed)
  have checked := c88 pattern guarded
  change d220 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_0 (pattern : Ten) : walkGuard ⟨29,15,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk27_0 : WalkBound ⟨29,15,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk27_1 (pattern : Ten) : walkGuard ⟨29,15,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk27_1 : WalkBound ⟨29,15,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk27_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_0 (pattern : Ten) : walkGuard ⟨29,30,.east⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk28_0 : WalkBound ⟨29,30,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk28_1 (pattern : Ten) : walkGuard ⟨29,30,.east⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk28_1 : WalkBound ⟨29,30,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk28_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_0 (pattern : Ten) : walkGuard ⟨29,43,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk29_0 : WalkBound ⟨29,43,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk29_1 (pattern : Ten) : walkGuard ⟨29,43,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk29_1 : WalkBound ⟨29,43,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk29_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_0 (pattern : Ten) : walkGuard ⟨29,16,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk30_0 : WalkBound ⟨29,16,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk30_1 (pattern : Ten) : walkGuard ⟨29,16,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk30_1 : WalkBound ⟨29,16,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk30_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_0 (pattern : Ten) : walkGuard ⟨29,44,.southEast⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk31_0 : WalkBound ⟨29,44,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk31_1 (pattern : Ten) : walkGuard ⟨29,44,.southEast⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk31_1 : WalkBound ⟨29,44,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk31_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_0 (pattern : Ten) : walkGuard ⟨30,16,.north⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk32_0 : WalkBound ⟨30,16,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk32_1 (pattern : Ten) : walkGuard ⟨30,16,.north⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk32_1 : WalkBound ⟨30,16,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk32_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_0 (pattern : Ten) : walkGuard ⟨30,31,.east⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk33_0 : WalkBound ⟨30,31,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk33_1 (pattern : Ten) : walkGuard ⟨30,31,.east⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem walk33_1 : WalkBound ⟨30,31,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk33_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_0 (pattern : Ten) : walkGuard ⟨30,44,.south⟩ 0 pattern = decide (d359 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk34_0 : WalkBound ⟨30,44,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d359 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_0]; exact allowed)
  have checked := c179 pattern guarded
  change d81 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk34_1 (pattern : Ten) : walkGuard ⟨30,44,.south⟩ 1 pattern = decide (d358 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk34_1 : WalkBound ⟨30,44,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d358 pattern = 1 := of_decide_eq_true (by rw [← guard_walk34_1]; exact allowed)
  have checked := c207 pattern guarded
  change d234 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
