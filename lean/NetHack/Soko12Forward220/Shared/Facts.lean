import NetHack.Soko12Forward220.Shared.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Shared
open NetHack.Sokoban
open NetHack.Sokoban.DecisionDAGTransform
theorem labels_strict (i j : Nat) (first : i < 89) (second : j < 89) (lt : i < j) : label i < label j := by
  have finite : ∀ i j : Fin 89, i.val < j.val → label i.val < label j.val := by decide +kernel
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
theorem gamma_after_phase5 (phase hero : Nat) (late : 6 ≤ phase) : gamma phase hero = 0 := by
  have h0 : phase ≠ 0 := by omega
  have h1 : phase ≠ 1 := by omega
  have h2 : phase ≠ 2 := by omega
  have h3 : phase ≠ 3 := by omega
  have h4 : phase ≠ 4 := by omega
  have h5 : phase ≠ 5 := by omega
  simp only [gamma, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

end NetHack.Soko12Forward220.Shared
