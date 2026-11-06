/- Full original3-2 lower138: old136 plus two units at the244 gate.
All actions, original holes, RLT and the original surplus4 are retained.
The attainable147 upper is a different theorem, not a matching minimum. -/
import NetHack.Soko32Gate138.Composition
namespace NetHack.Soko32Gate138
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection NetHack.Sokoban.LowerBounds
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem value_eq (state : State) (good : Good soko3_2.board soko3_2.initial.holes prior.allowance state) :
    value certificate state = value prior state + gate state.player (project state.boulders) := by
  have nextGood : Good soko3_2.board soko3_2.initial.holes certificate.allowance state := by
    change Good soko3_2.board soko3_2.initial.holes prior.allowance state
    exact good
  simp only [value,correction,if_pos good,if_pos nextGood]
  change potential.value state + bonus state.player (project state.boulders) =
    potential.value state + prior.bonus state.player (project state.boulders) + gate state.player (project state.boulders)
  unfold bonus
  omega
theorem initial_value : value certificate soko3_2.initial = 138 := by
  have good : Good soko3_2.board soko3_2.initial.holes prior.allowance soko3_2.initial := by decide +kernel
  have bit : gate soko3_2.initial.player (project soko3_2.initial.boulders) = 2 := by decide +kernel
  rw [value_eq soko3_2.initial good,NetHack.Sokoban32Refined.initial_value,bit]
  decide +kernel
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions final pushes moves)
    (completed : Goal final) : 138 ≤ pushes :=
  pushes_minimal_of_potential (stepBound certificate Generated.soko3_2_potential_valid)
    (goalBound certificate Generated.soko3_2_potential_valid) 138 initial_value trace completed
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_2.board soko3_2.initial directions final pushes moves)
    (completed : Goal final) : 138 ≤ moves :=
  Nat.le_trans (pushes_lower_bound trace completed) (trace_pushes_le_moves trace)
end NetHack.Soko32Gate138
