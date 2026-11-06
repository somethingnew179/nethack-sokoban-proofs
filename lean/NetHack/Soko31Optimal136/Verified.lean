import NetHack.Soko31Optimal136.Row0
import NetHack.Soko31Optimal136.Row1
import NetHack.Soko31Optimal136.Row2
import NetHack.Soko31Optimal136.Row3
import NetHack.Soko31Sparse134.Verified
import NetHack.Soko31Witness136.Soko31Macro136M270Solution
namespace NetHack.Soko31Optimal136
open NetHack.Sokoban NetHack.Sokoban.FiniteResidual
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_rows : All (RowBound soko3_1.board base norm table key) table :=
  ⟨bound0, ⟨bound1, ⟨bound3, True.intro, True.intro⟩, True.intro⟩, ⟨bound2, True.intro, True.intro⟩⟩
theorem initial_value : corrected base norm table key soko3_1.initial = 136 := by decide +kernel
/-- Any completing ORIGINAL3-1 Trace has at least136 initiated pushes.
No premise on a solver, final surplus placement or extra puzzle restriction. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves)
    (completed : Goal final) : 136 ≤ pushes :=
  FiniteResidualGuarded.pushes_lower_bound base (HazardPhases.Good NetHack.Soko31Sparse134.phases)
    norm table key
    (NetHack.Soko31Sparse134.step_bound NetHack.Soko31Sparse134.all_checked)
    (HazardPhases.step_good NetHack.Soko31Sparse134.phases)
    NetHack.Soko31Sparse134.value_respects
    (fun s goal => by
      change NetHack.Soko31Sparse134.value s ≤ 0
      rw [NetHack.Soko31Sparse134.value_goal_zero s goal]
      exact Int.le_refl 0)
    all_rows NetHack.Soko31Hero135.goal_free NetHack.Sokoban31Phases.initial_good 136 initial_value trace completed
/-- Exact original-start push minimum. The witness has270 successful hero
movements; their minimum and full-game NetHack optimality are not claimed. -/
theorem minimum136 :
    (∃ directions final moves, Trace soko3_1.board soko3_1.initial directions final 136 moves ∧ Goal final) ∧
    (∀ directions final pushes moves, Trace soko3_1.board soko3_1.initial directions final pushes moves →
      Goal final → 136 ≤ pushes) :=
  ⟨⟨Generated.soko3_1Macro136M270Path,Generated.soko3_1Macro136M270FinalState,270,
      Generated.soko3_1_macro136_m270_trace,Generated.soko3_1_macro136_m270_goal⟩,
    fun _ _ _ _ trace completed => pushes_lower_bound trace completed⟩
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves)
    (completed : Goal final) : 136 ≤ moves :=
  Nat.le_trans (pushes_lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)
end NetHack.Soko31Optimal136
