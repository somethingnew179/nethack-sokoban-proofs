import NetHack.Soko31Hero135.Row0
import NetHack.Soko31Hero135.Row1
import NetHack.Soko31Hero135.Row2
import NetHack.Soko31Hero135.Row3
namespace NetHack.Soko31Hero135
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
/-- All literal occupancy rows cover all actual Model actions. -/
theorem all_rows : All (RowBound soko3_1.board base norm table key) table :=
  ⟨bound0, ⟨bound1, ⟨bound3, True.intro, True.intro⟩, True.intro⟩, ⟨bound2, True.intro, True.intro⟩⟩
theorem goal_free : All (fun entry => entry.holes ≠ []) table := by
  simp only [table, All]
  decide +kernel
theorem initial_bonus : bonus norm table key soko3_1.initial = 2 := by decide +kernel
theorem initial_value : corrected base norm table key soko3_1.initial = 135 := by
  unfold corrected
  rw [base_eq, NetHack.Soko31Hero133.proposed_initial_value, initial_bonus]
  decide +kernel
/-- Universal lower135 for the full original3-1 initial Model.Trace. Not a
minimum135: the currently checked completing path costs137 pushes. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves)
    (completed : Goal final) : 135 ≤ pushes :=
  HeroPhasePotential.Residual.pushes_lower_bound cert norm table key all_rows goal_free
    NetHack.Sokoban31Phases.initial_good 135 initial_value trace completed
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves)
    (completed : Goal final) : 135 ≤ moves :=
  Nat.le_trans (pushes_lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)
end NetHack.Soko31Hero135
