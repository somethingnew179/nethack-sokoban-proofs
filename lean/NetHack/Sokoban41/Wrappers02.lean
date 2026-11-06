/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers01
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk70_0 (pattern : Ten) : walkGuard ⟨39,38,.west⟩ 0 pattern = decide (d354 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk70_0 : WalkBound ⟨39,38,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d354 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_0]; exact allowed)
  have checked := c73 pattern guarded
  change d66 pattern ≤ d85 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk70_1 (pattern : Ten) : walkGuard ⟨39,38,.west⟩ 1 pattern = decide (d353 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk70_1 : WalkBound ⟨39,38,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d353 pattern = 1 := of_decide_eq_true (by rw [← guard_walk70_1]; exact allowed)
  have checked := c88 pattern guarded
  change d220 pattern ≤ d238 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_0 (pattern : Ten) : walkGuard ⟨39,52,.southWest⟩ 0 pattern = decide (d367 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk71_0 : WalkBound ⟨39,52,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d367 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_0]; exact allowed)
  have checked := c333 pattern guarded
  change d66 pattern ≤ d135 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk71_1 (pattern : Ten) : walkGuard ⟨39,52,.southWest⟩ 1 pattern = decide (d382 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem walk71_1 : WalkBound ⟨39,52,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d382 pattern = 1 := of_decide_eq_true (by rw [← guard_walk71_1]; exact allowed)
  have checked := c338 pattern guarded
  change d220 pattern ≤ d291 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_0 (pattern : Ten) : walkGuard ⟨39,24,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk72_0 : WalkBound ⟨39,24,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_0]; exact allowed)
  have checked := c59 pattern guarded
  change d66 pattern ≤ d66 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk72_1 (pattern : Ten) : walkGuard ⟨39,24,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem walk72_1 : WalkBound ⟨39,24,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk72_1]; exact allowed)
  have checked := c60 pattern guarded
  change d220 pattern ≤ d220 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_0 (pattern : Ten) : walkGuard ⟨43,29,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk73_0 : WalkBound ⟨43,29,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk73_1 (pattern : Ten) : walkGuard ⟨43,29,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk73_1 : WalkBound ⟨43,29,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk73_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_0 (pattern : Ten) : walkGuard ⟨43,44,.east⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk74_0 : WalkBound ⟨43,44,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk74_1 (pattern : Ten) : walkGuard ⟨43,44,.east⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk74_1 : WalkBound ⟨43,44,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk74_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk75_0 (pattern : Ten) : walkGuard ⟨43,57,.south⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk75_0 : WalkBound ⟨43,57,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk75_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk75_1 (pattern : Ten) : walkGuard ⟨43,57,.south⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk75_1 : WalkBound ⟨43,57,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk75_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk76_0 (pattern : Ten) : walkGuard ⟨43,30,.northEast⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk76_0 : WalkBound ⟨43,30,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk76_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk76_1 (pattern : Ten) : walkGuard ⟨43,30,.northEast⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk76_1 : WalkBound ⟨43,30,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk76_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk77_0 (pattern : Ten) : walkGuard ⟨43,58,.southEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk77_0 : WalkBound ⟨43,58,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk77_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk77_1 (pattern : Ten) : walkGuard ⟨43,58,.southEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk77_1 : WalkBound ⟨43,58,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk77_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk78_0 (pattern : Ten) : walkGuard ⟨44,30,.north⟩ 0 pattern = decide (d359 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk78_0 : WalkBound ⟨44,30,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d359 pattern = 1 := of_decide_eq_true (by rw [← guard_walk78_0]; exact allowed)
  have checked := c355 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk78_1 (pattern : Ten) : walkGuard ⟨44,30,.north⟩ 1 pattern = decide (d358 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk78_1 : WalkBound ⟨44,30,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d358 pattern = 1 := of_decide_eq_true (by rw [← guard_walk78_1]; exact allowed)
  have checked := c382 pattern guarded
  change d248 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk79_0 (pattern : Ten) : walkGuard ⟨44,45,.east⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk79_0 : WalkBound ⟨44,45,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk79_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk79_1 (pattern : Ten) : walkGuard ⟨44,45,.east⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk79_1 : WalkBound ⟨44,45,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk79_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk80_0 (pattern : Ten) : walkGuard ⟨44,58,.south⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk80_0 : WalkBound ⟨44,58,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk80_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk80_1 (pattern : Ten) : walkGuard ⟨44,58,.south⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk80_1 : WalkBound ⟨44,58,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk80_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk81_0 (pattern : Ten) : walkGuard ⟨44,43,.west⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk81_0 : WalkBound ⟨44,43,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk81_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk81_1 (pattern : Ten) : walkGuard ⟨44,43,.west⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk81_1 : WalkBound ⟨44,43,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk81_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk82_0 (pattern : Ten) : walkGuard ⟨44,31,.northEast⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk82_0 : WalkBound ⟨44,31,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk82_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk82_1 (pattern : Ten) : walkGuard ⟨44,31,.northEast⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk82_1 : WalkBound ⟨44,31,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk82_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk83_0 (pattern : Ten) : walkGuard ⟨44,57,.southWest⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk83_0 : WalkBound ⟨44,57,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk83_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk83_1 (pattern : Ten) : walkGuard ⟨44,57,.southWest⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk83_1 : WalkBound ⟨44,57,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk83_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk84_0 (pattern : Ten) : walkGuard ⟨44,29,.northWest⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk84_0 : WalkBound ⟨44,29,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk84_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk84_1 (pattern : Ten) : walkGuard ⟨44,29,.northWest⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk84_1 : WalkBound ⟨44,29,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk84_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk85_0 (pattern : Ten) : walkGuard ⟨45,31,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk85_0 : WalkBound ⟨45,31,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk85_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk85_1 (pattern : Ten) : walkGuard ⟨45,31,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk85_1 : WalkBound ⟨45,31,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk85_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk86_0 (pattern : Ten) : walkGuard ⟨45,46,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk86_0 : WalkBound ⟨45,46,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk86_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk86_1 (pattern : Ten) : walkGuard ⟨45,46,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk86_1 : WalkBound ⟨45,46,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk86_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk87_0 (pattern : Ten) : walkGuard ⟨45,44,.west⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk87_0 : WalkBound ⟨45,44,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk87_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk87_1 (pattern : Ten) : walkGuard ⟨45,44,.west⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk87_1 : WalkBound ⟨45,44,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk87_1]; exact allowed)
  have checked := c108 pattern guarded
  change d192 pattern ≤ d248 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_0 (pattern : Ten) : walkGuard ⟨45,32,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk88_0 : WalkBound ⟨45,32,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk88_1 (pattern : Ten) : walkGuard ⟨45,32,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk88_1 : WalkBound ⟨45,32,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk88_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_0 (pattern : Ten) : walkGuard ⟨45,58,.southWest⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk89_0 : WalkBound ⟨45,58,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk89_1 (pattern : Ten) : walkGuard ⟨45,58,.southWest⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem walk89_1 : WalkBound ⟨45,58,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_walk89_1]; exact allowed)
  have checked := c392 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_0 (pattern : Ten) : walkGuard ⟨45,30,.northWest⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk90_0 : WalkBound ⟨45,30,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_0]; exact allowed)
  have checked := c27 pattern guarded
  change d37 pattern ≤ d81 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk90_1 (pattern : Ten) : walkGuard ⟨45,30,.northWest⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem walk90_1 : WalkBound ⟨45,30,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_walk90_1]; exact allowed)
  have checked := c58 pattern guarded
  change d192 pattern ≤ d234 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_0 (pattern : Ten) : walkGuard ⟨46,32,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk91_0 : WalkBound ⟨46,32,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk91_1 (pattern : Ten) : walkGuard ⟨46,32,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk91_1 : WalkBound ⟨46,32,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk91_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_0 (pattern : Ten) : walkGuard ⟨46,47,.east⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk92_0 : WalkBound ⟨46,47,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk92_1 (pattern : Ten) : walkGuard ⟨46,47,.east⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk92_1 : WalkBound ⟨46,47,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk92_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_0 (pattern : Ten) : walkGuard ⟨46,45,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk93_0 : WalkBound ⟨46,45,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk93_1 (pattern : Ten) : walkGuard ⟨46,45,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk93_1 : WalkBound ⟨46,45,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk93_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_0 (pattern : Ten) : walkGuard ⟨46,31,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk94_0 : WalkBound ⟨46,31,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk94_1 (pattern : Ten) : walkGuard ⟨46,31,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk94_1 : WalkBound ⟨46,31,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk94_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_0 (pattern : Ten) : walkGuard ⟨47,48,.east⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk95_0 : WalkBound ⟨47,48,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_0]; exact allowed)
  have checked := c428 pattern guarded
  change d37 pattern ≤ d107 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk95_1 (pattern : Ten) : walkGuard ⟨47,48,.east⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk95_1 : WalkBound ⟨47,48,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk95_1]; exact allowed)
  have checked := c455 pattern guarded
  change d192 pattern ≤ d265 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_0 (pattern : Ten) : walkGuard ⟨47,46,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk96_0 : WalkBound ⟨47,46,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk96_1 (pattern : Ten) : walkGuard ⟨47,46,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk96_1 : WalkBound ⟨47,46,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk96_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_0 (pattern : Ten) : walkGuard ⟨47,62,.southEast⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk97_0 : WalkBound ⟨47,62,.southEast⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_0]; exact allowed)
  have checked := c480 pattern guarded
  change d37 pattern ≤ d149 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk97_1 (pattern : Ten) : walkGuard ⟨47,62,.southEast⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk97_1 : WalkBound ⟨47,62,.southEast⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk97_1]; exact allowed)
  have checked := c498 pattern guarded
  change d192 pattern ≤ d308 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_0 (pattern : Ten) : walkGuard ⟨47,32,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk98_0 : WalkBound ⟨47,32,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk98_1 (pattern : Ten) : walkGuard ⟨47,32,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk98_1 : WalkBound ⟨47,32,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk98_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_0 (pattern : Ten) : walkGuard ⟨48,49,.east⟩ 0 pattern = decide (d387 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk99_0 : WalkBound ⟨48,49,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d387 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_0]; exact allowed)
  have checked := c533 pattern guarded
  change d107 pattern ≤ d123 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk99_1 (pattern : Ten) : walkGuard ⟨48,49,.east⟩ 1 pattern = decide (d388 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk99_1 : WalkBound ⟨48,49,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d388 pattern = 1 := of_decide_eq_true (by rw [← guard_walk99_1]; exact allowed)
  have checked := c559 pattern guarded
  change d265 pattern ≤ d279 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk100_0 (pattern : Ten) : walkGuard ⟨48,62,.south⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk100_0 : WalkBound ⟨48,62,.south⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_0]; exact allowed)
  have checked := c584 pattern guarded
  change d107 pattern ≤ d149 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk100_1 (pattern : Ten) : walkGuard ⟨48,62,.south⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk100_1 : WalkBound ⟨48,62,.south⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk100_1]; exact allowed)
  have checked := c602 pattern guarded
  change d265 pattern ≤ d308 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_0 (pattern : Ten) : walkGuard ⟨48,47,.west⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk101_0 : WalkBound ⟨48,47,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_0]; exact allowed)
  have checked := c617 pattern guarded
  change d107 pattern ≤ d37 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk101_1 (pattern : Ten) : walkGuard ⟨48,47,.west⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem walk101_1 : WalkBound ⟨48,47,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_walk101_1]; exact allowed)
  have checked := c626 pattern guarded
  change d265 pattern ≤ d192 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_0 (pattern : Ten) : walkGuard ⟨49,50,.east⟩ 0 pattern = decide (d390 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> rfl
theorem walk102_0 : WalkBound ⟨49,50,.east⟩ 0 := by
  intro pattern allowed
  have guarded : d390 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_0]; exact allowed)
  have checked := c658 pattern guarded
  change d123 pattern ≤ d132 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk102_1 (pattern : Ten) : walkGuard ⟨49,50,.east⟩ 1 pattern = decide (d391 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> rfl
theorem walk102_1 : WalkBound ⟨49,50,.east⟩ 1 := by
  intro pattern allowed
  have guarded : d391 pattern = 1 := of_decide_eq_true (by rw [← guard_walk102_1]; exact allowed)
  have checked := c684 pattern guarded
  change d279 pattern ≤ d288 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_0 (pattern : Ten) : walkGuard ⟨49,48,.west⟩ 0 pattern = decide (d387 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk103_0 : WalkBound ⟨49,48,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d387 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_0]; exact allowed)
  have checked := c712 pattern guarded
  change d123 pattern ≤ d107 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk103_1 (pattern : Ten) : walkGuard ⟨49,48,.west⟩ 1 pattern = decide (d388 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk103_1 : WalkBound ⟨49,48,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d388 pattern = 1 := of_decide_eq_true (by rw [← guard_walk103_1]; exact allowed)
  have checked := c733 pattern guarded
  change d279 pattern ≤ d265 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_0 (pattern : Ten) : walkGuard ⟨49,62,.southWest⟩ 0 pattern = decide (d387 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk104_0 : WalkBound ⟨49,62,.southWest⟩ 0 := by
  intro pattern allowed
  have guarded : d387 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_0]; exact allowed)
  have checked := c761 pattern guarded
  change d123 pattern ≤ d149 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk104_1 (pattern : Ten) : walkGuard ⟨49,62,.southWest⟩ 1 pattern = decide (d388 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem walk104_1 : WalkBound ⟨49,62,.southWest⟩ 1 := by
  intro pattern allowed
  have guarded : d388 pattern = 1 := of_decide_eq_true (by rw [← guard_walk104_1]; exact allowed)
  have checked := c782 pattern guarded
  change d279 pattern ≤ d308 pattern
  simpa only [Int.zero_add] using checked
end NetHack.Sokoban41
