/- Reflection transfers the actual individual-move semantics, with both exact
costs, in both directions. No quotient of player positions is used. -/
import NetHack.Sokoban.Symmetry.Isomorphism

namespace NetHack.Sokoban.Symmetry
namespace BoardIsomorphism

def inverse {board : Board} (iso : BoardIsomorphism board) :
    BoardIsomorphism (mapBoard iso.cells board) := {
  cells := iso.cells
  directions := iso.directions
  advance := by
    intro cell direction
    rw [board_involutive]
    have reflected := congrArg (Option.map iso.cells.apply)
      (iso.advance (iso.cells.apply cell) (iso.directions.apply direction))
    simpa only [iso.cells.involutive, iso.directions.involutive, option_involutive]
      using reflected.symm }

theorem trace_map {board : Board} (iso : BoardIsomorphism board)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    Trace (mapBoard iso.cells board) (mapState iso.cells initial)
      (directions.map iso.directions.apply) (mapState iso.cells final) pushes moves := by
  induction trace with
  | nil state => exact Trace.nil _
  | @cons state direction next rest final pushes moves head tail ih =>
    have checked : step (mapBoard iso.cells board) (mapState iso.cells state)
        (iso.directions.apply direction) = some (mapTransition iso.cells next) := by
      rw [iso.step_map, head]
      rfl
    exact Trace.cons (next := mapTransition iso.cells next) checked ih

theorem trace_back {board : Board} (iso : BoardIsomorphism board)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace (mapBoard iso.cells board) (mapState iso.cells initial)
      directions final pushes moves) :
    Trace board initial (directions.map iso.directions.apply)
      (mapState iso.cells final) pushes moves := by
  have pulled := iso.inverse.trace_map trace
  simpa only [inverse, board_involutive, state_involutive] using pulled

theorem goal_map_iff (perm : CellPermutation) (state : State) :
    Goal (mapState perm state) ↔ Goal state := by
  simp only [Goal, state_holes, List.map_eq_nil_iff]

end BoardIsomorphism
end NetHack.Sokoban.Symmetry
