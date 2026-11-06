/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers05
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk210_0 (pattern : Ten) : walkGuard ⟨108,94,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk210_0 : WalkBound ⟨108,94,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk210_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk210_1 (pattern : Ten) : walkGuard ⟨108,94,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk210_1 : WalkBound ⟨108,94,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk210_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk211_0 (pattern : Ten) : walkGuard ⟨108,109,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk211_0 : WalkBound ⟨108,109,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk211_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk211_1 (pattern : Ten) : walkGuard ⟨108,109,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk211_1 : WalkBound ⟨108,109,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk211_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk212_0 (pattern : Ten) : walkGuard ⟨108,122,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk212_0 : WalkBound ⟨108,122,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk212_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk212_1 (pattern : Ten) : walkGuard ⟨108,122,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk212_1 : WalkBound ⟨108,122,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk212_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk213_0 (pattern : Ten) : walkGuard ⟨108,107,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk213_0 : WalkBound ⟨108,107,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk213_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk213_1 (pattern : Ten) : walkGuard ⟨108,107,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk213_1 : WalkBound ⟨108,107,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk213_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk214_0 (pattern : Ten) : walkGuard ⟨108,95,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk214_0 : WalkBound ⟨108,95,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk214_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk214_1 (pattern : Ten) : walkGuard ⟨108,95,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk214_1 : WalkBound ⟨108,95,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk214_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk215_0 (pattern : Ten) : walkGuard ⟨108,123,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk215_0 : WalkBound ⟨108,123,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk215_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk215_1 (pattern : Ten) : walkGuard ⟨108,123,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk215_1 : WalkBound ⟨108,123,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk215_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk216_0 (pattern : Ten) : walkGuard ⟨108,121,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk216_0 : WalkBound ⟨108,121,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk216_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk216_1 (pattern : Ten) : walkGuard ⟨108,121,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk216_1 : WalkBound ⟨108,121,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk216_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk217_0 (pattern : Ten) : walkGuard ⟨108,93,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk217_0 : WalkBound ⟨108,93,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk217_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk217_1 (pattern : Ten) : walkGuard ⟨108,93,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk217_1 : WalkBound ⟨108,93,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk217_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk218_0 (pattern : Ten) : walkGuard ⟨109,95,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk218_0 : WalkBound ⟨109,95,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk218_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk218_1 (pattern : Ten) : walkGuard ⟨109,95,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk218_1 : WalkBound ⟨109,95,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk218_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk219_0 (pattern : Ten) : walkGuard ⟨109,110,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk219_0 : WalkBound ⟨109,110,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk219_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk219_1 (pattern : Ten) : walkGuard ⟨109,110,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk219_1 : WalkBound ⟨109,110,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk219_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk220_0 (pattern : Ten) : walkGuard ⟨109,123,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk220_0 : WalkBound ⟨109,123,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk220_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk220_1 (pattern : Ten) : walkGuard ⟨109,123,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk220_1 : WalkBound ⟨109,123,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk220_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk221_0 (pattern : Ten) : walkGuard ⟨109,108,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk221_0 : WalkBound ⟨109,108,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk221_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk221_1 (pattern : Ten) : walkGuard ⟨109,108,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk221_1 : WalkBound ⟨109,108,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk221_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk222_0 (pattern : Ten) : walkGuard ⟨109,96,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk222_0 : WalkBound ⟨109,96,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk222_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk222_1 (pattern : Ten) : walkGuard ⟨109,96,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk222_1 : WalkBound ⟨109,96,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk222_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk223_0 (pattern : Ten) : walkGuard ⟨109,124,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk223_0 : WalkBound ⟨109,124,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk223_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk223_1 (pattern : Ten) : walkGuard ⟨109,124,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk223_1 : WalkBound ⟨109,124,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk223_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk224_0 (pattern : Ten) : walkGuard ⟨109,122,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk224_0 : WalkBound ⟨109,122,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk224_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk224_1 (pattern : Ten) : walkGuard ⟨109,122,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk224_1 : WalkBound ⟨109,122,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk224_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk225_0 (pattern : Ten) : walkGuard ⟨109,94,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk225_0 : WalkBound ⟨109,94,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk225_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk225_1 (pattern : Ten) : walkGuard ⟨109,94,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk225_1 : WalkBound ⟨109,94,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk225_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk226_0 (pattern : Ten) : walkGuard ⟨110,96,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk226_0 : WalkBound ⟨110,96,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk226_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk226_1 (pattern : Ten) : walkGuard ⟨110,96,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk226_1 : WalkBound ⟨110,96,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk226_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk227_0 (pattern : Ten) : walkGuard ⟨110,124,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk227_0 : WalkBound ⟨110,124,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk227_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk227_1 (pattern : Ten) : walkGuard ⟨110,124,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk227_1 : WalkBound ⟨110,124,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk227_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk228_0 (pattern : Ten) : walkGuard ⟨110,109,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk228_0 : WalkBound ⟨110,109,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk228_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk228_1 (pattern : Ten) : walkGuard ⟨110,109,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk228_1 : WalkBound ⟨110,109,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk228_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk229_0 (pattern : Ten) : walkGuard ⟨110,123,.southWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk229_0 : WalkBound ⟨110,123,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk229_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk229_1 (pattern : Ten) : walkGuard ⟨110,123,.southWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk229_1 : WalkBound ⟨110,123,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk229_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk230_0 (pattern : Ten) : walkGuard ⟨110,95,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk230_0 : WalkBound ⟨110,95,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk230_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk230_1 (pattern : Ten) : walkGuard ⟨110,95,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk230_1 : WalkBound ⟨110,95,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk230_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk231_0 (pattern : Ten) : walkGuard ⟨114,100,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk231_0 : WalkBound ⟨114,100,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk231_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk231_1 (pattern : Ten) : walkGuard ⟨114,100,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk231_1 : WalkBound ⟨114,100,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk231_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk232_0 (pattern : Ten) : walkGuard ⟨114,128,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk232_0 : WalkBound ⟨114,128,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk232_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk232_1 (pattern : Ten) : walkGuard ⟨114,128,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk232_1 : WalkBound ⟨114,128,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk232_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk233_0 (pattern : Ten) : walkGuard ⟨114,99,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk233_0 : WalkBound ⟨114,99,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk233_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk233_1 (pattern : Ten) : walkGuard ⟨114,99,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk233_1 : WalkBound ⟨114,99,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk233_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk234_0 (pattern : Ten) : walkGuard ⟨120,106,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk234_0 : WalkBound ⟨120,106,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk234_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk234_1 (pattern : Ten) : walkGuard ⟨120,106,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk234_1 : WalkBound ⟨120,106,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk234_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk235_0 (pattern : Ten) : walkGuard ⟨120,121,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk235_0 : WalkBound ⟨120,121,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk235_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk235_1 (pattern : Ten) : walkGuard ⟨120,121,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk235_1 : WalkBound ⟨120,121,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk235_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk236_0 (pattern : Ten) : walkGuard ⟨120,134,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk236_0 : WalkBound ⟨120,134,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk236_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk236_1 (pattern : Ten) : walkGuard ⟨120,134,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk236_1 : WalkBound ⟨120,134,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk236_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk237_0 (pattern : Ten) : walkGuard ⟨120,107,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk237_0 : WalkBound ⟨120,107,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk237_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk237_1 (pattern : Ten) : walkGuard ⟨120,107,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk237_1 : WalkBound ⟨120,107,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk237_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_0 (pattern : Ten) : walkGuard ⟨120,135,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk238_0 : WalkBound ⟨120,135,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk238_1 (pattern : Ten) : walkGuard ⟨120,135,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk238_1 : WalkBound ⟨120,135,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk238_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_0 (pattern : Ten) : walkGuard ⟨121,107,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk239_0 : WalkBound ⟨121,107,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk239_1 (pattern : Ten) : walkGuard ⟨121,107,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk239_1 : WalkBound ⟨121,107,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk239_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_0 (pattern : Ten) : walkGuard ⟨121,122,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk240_0 : WalkBound ⟨121,122,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk240_1 (pattern : Ten) : walkGuard ⟨121,122,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk240_1 : WalkBound ⟨121,122,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk240_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_0 (pattern : Ten) : walkGuard ⟨121,135,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk241_0 : WalkBound ⟨121,135,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk241_1 (pattern : Ten) : walkGuard ⟨121,135,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk241_1 : WalkBound ⟨121,135,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk241_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_0 (pattern : Ten) : walkGuard ⟨121,120,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk242_0 : WalkBound ⟨121,120,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk242_1 (pattern : Ten) : walkGuard ⟨121,120,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk242_1 : WalkBound ⟨121,120,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk242_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_0 (pattern : Ten) : walkGuard ⟨121,108,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk243_0 : WalkBound ⟨121,108,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk243_1 (pattern : Ten) : walkGuard ⟨121,108,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk243_1 : WalkBound ⟨121,108,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk243_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_0 (pattern : Ten) : walkGuard ⟨121,136,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk244_0 : WalkBound ⟨121,136,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk244_1 (pattern : Ten) : walkGuard ⟨121,136,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk244_1 : WalkBound ⟨121,136,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk244_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
