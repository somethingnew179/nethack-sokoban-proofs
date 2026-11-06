import NetHack.Soko12Forward219.Shared.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Shared
open NetHack.Sokoban
open NetHack.Sokoban.DecisionDAGTransform
theorem labels_strict (i j : Nat) (first : i < 50) (second : j < 50) (lt : i < j) : label i < label j := by
  have finite : ∀ i j : Fin 50, i.val < j.val → label i.val < label j.val := by decide +kernel
  exact finite ⟨i, first⟩ ⟨j, second⟩ lt
theorem reader_ordered : Ordered read := RankedDAG.reader_ordered cfg (by decide +kernel) labels_strict
theorem reader_supported : Supported read cells := by
  have support : (List.range cfg.count).map cfg.label = cells := by decide +kernel
  rw [← support]
  exact RankedDAG.reader_supported cfg
theorem all_bounds_checks (root : Nat) : DecisionDAGBounds.check read bounds root = true := RankedDAG.all_bounds_checks cfg root
theorem eval_nonnegative (p : DecisionDAG.Pattern) (root : Nat) : 0 ≤ DecisionDAG.eval read p root := RankedDAG.eval_nonnegative cfg p root
/-- Explicit value5, using the existing guard's literal fallback semantics. -/
theorem literal5_checked : read literal5Root = .literal 5 := by decide +kernel
theorem gamma_after_phase0 (phase hero : Nat) (positive : 0 < phase) : gamma phase hero = 0 := by simp [gamma, show phase ≠ 0 by omega]

end NetHack.Soko12Forward219.Shared
