import NetHack.Soko11Hero315.AllRows
namespace NetHack.Soko11Hero315
open NetHack.Sokoban
/-- Every completing ORIGINAL soko1-1 Model Trace; exact push cost.
This lower bound alone does not claim matching upper cost or optimality. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves)
    (completed : Goal final) : 315 ≤ pushes :=
  lower_bound_if_all_scalar_rows all_walk_rows all_push_rows all_advance_rows trace completed
/-- Lower bound on successful Model displacements, not a moves optimum or
ticks/penalties in the full game. -/
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_1.board soko1_1.initial directions final pushes moves)
    (completed : Goal final) : 315 ≤ moves :=
  Nat.le_trans (pushes_lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)
end NetHack.Soko11Hero315
