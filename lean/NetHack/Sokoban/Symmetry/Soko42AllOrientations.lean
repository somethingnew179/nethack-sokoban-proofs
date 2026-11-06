/- All4 actual creation orientations of pinned soko4-2.
The universal lower bound is pulled back through the proven inverse exact
move semantics. The332-move witness is not asserted moves-optimal. -/
import NetHack.Sokoban.Symmetry.Soko42Reflections

namespace NetHack.Sokoban.Symmetry.Soko42AllOrientations
open Soko42Reflections

theorem transferred (iso : BoardIsomorphism soko4_2.board) :
    Trace (mapBoard iso.cells soko4_2.board) (mapState iso.cells soko4_2.initial)
      (Generated.soko4_2CandidatePath.map iso.directions.apply)
      (mapState iso.cells Generated.soko4_2CandidateFinalState) 85 332 ∧
    Goal (mapState iso.cells Generated.soko4_2CandidateFinalState) ∧
    (∀ directions final pushes moves,
      Trace (mapBoard iso.cells soko4_2.board) (mapState iso.cells soko4_2.initial)
        directions final pushes moves → Goal final → 85 ≤ pushes) := by
  refine ⟨iso.trace_map Generated.soko4_2_candidate_trace,
    (BoardIsomorphism.goal_map_iff iso.cells _).mpr Generated.soko4_2_candidate_goal, ?_⟩
  intro directions final pushes moves trace completed
  exact Soko42Optimal.lower_bound (iso.trace_back trace)
    ((BoardIsomorphism.goal_map_iff iso.cells final).mpr completed)

inductive Orientation where
  | canonical | horizontal | vertical | both
  deriving Repr, DecidableEq

def board : Orientation → Board
  | .canonical => soko4_2.board
  | .horizontal => mapBoard horizontal.cells soko4_2.board
  | .vertical => mapBoard vertical.cells soko4_2.board
  | .both => mapBoard both.cells soko4_2.board

def initial : Orientation → State
  | .canonical => soko4_2.initial
  | .horizontal => mapState horizontal.cells soko4_2.initial
  | .vertical => mapState vertical.cells soko4_2.initial
  | .both => mapState both.cells soko4_2.initial

def path : Orientation → List Dir
  | .canonical => Generated.soko4_2CandidatePath
  | .horizontal => Generated.soko4_2CandidatePath.map horizontal.directions.apply
  | .vertical => Generated.soko4_2CandidatePath.map vertical.directions.apply
  | .both => Generated.soko4_2CandidatePath.map both.directions.apply

def final : Orientation → State
  | .canonical => Generated.soko4_2CandidateFinalState
  | .horizontal => mapState horizontal.cells Generated.soko4_2CandidateFinalState
  | .vertical => mapState vertical.cells Generated.soko4_2CandidateFinalState
  | .both => mapState both.cells Generated.soko4_2CandidateFinalState

/-- Each actual orientation has a winning85-push332-move trace and every
winning trace in the explicitly restricted profile needs at least85 pushes. -/
theorem optimal (orientation : Orientation) :
    Trace (board orientation) (initial orientation) (path orientation) (final orientation) 85 332 ∧
    Goal (final orientation) ∧
    (∀ directions endState pushes moves,
      Trace (board orientation) (initial orientation) directions endState pushes moves →
      Goal endState → 85 ≤ pushes) := by
  cases orientation with
  | canonical => exact Soko42Optimal.optimal
  | horizontal => exact transferred horizontal
  | vertical => exact transferred vertical
  | both => exact transferred both

/-- The moves metric remains separate:85 is a lower bound,332 is a checked
upper bound. This theorem makes no moves-minimality claim. -/
theorem moves_lower_bound (orientation : Orientation)
    {directions : List Dir} {endState : State} {pushes moves : Nat}
    (trace : Trace (board orientation) (initial orientation) directions endState pushes moves)
    (completed : Goal endState) : 85 ≤ moves :=
  Nat.le_trans ((optimal orientation).2.2 _ _ _ _ trace completed)
    (LowerBounds.trace_pushes_le_moves trace)

theorem every_suffix_optimal (orientation : Orientation) (first second : List Dir)
    (splitPath : first ++ second = path orientation) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace (board orientation) (initial orientation) first middle firstPushes firstMoves ∧
      Trace (board orientation) middle second (final orientation) secondPushes secondMoves ∧
      85 = firstPushes + secondPushes ∧ 332 = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace (board orientation) middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) := by
  have whole : Trace (board orientation) (initial orientation) (first ++ second)
      (final orientation) 85 332 := by
    rw [splitPath]
    exact (optimal orientation).1
  exact Reduction.every_suffix_optimal first second
    (optimal orientation).2.2 whole (optimal orientation).2.1

end NetHack.Sokoban.Symmetry.Soko42AllOrientations
