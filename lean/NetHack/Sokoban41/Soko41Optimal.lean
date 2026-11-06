/- Exact push optimum for the complete real soko4-1 source map.
Profile is the frozen Model's deterministic rolling/no-collision pure puzzle.
The299 individual moves of the witness are not asserted moves-minimal. -/
import NetHack.Sokoban41.Numerics
namespace NetHack.Sokoban41
open NetHack.Sokoban
open Generated

theorem soko4_1_pushes_optimal :
    Trace soko4_1.board soko4_1.initial soko4_1CandidatePath soko4_1CandidateFinalState 80 299 ∧
    Goal soko4_1CandidateFinalState ∧
    (∀ directions final pushes moves,
      Trace soko4_1.board soko4_1.initial directions final pushes moves → Goal final → 80 ≤ pushes) :=
  Optimality.optimal Numerics.numericBounds

theorem soko4_1_pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves) (completed : Goal final) :
    80 ≤ pushes := Optimality.lower_bound Numerics.numericBounds trace completed

/-- A lower bound on individual moves, not a claim that299 is minimal. -/
theorem soko4_1_moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves) (completed : Goal final) :
    80 ≤ moves := Optimality.moves_lower_bound Numerics.numericBounds trace completed

theorem soko4_1_every_suffix_optimal (first second : List Dir)
    (splitPath : first ++ second = soko4_1CandidatePath) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace soko4_1.board soko4_1.initial first middle firstPushes firstMoves ∧
      Trace soko4_1.board middle second soko4_1CandidateFinalState secondPushes secondMoves ∧
      80 = firstPushes + secondPushes ∧ 299 = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace soko4_1.board middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) :=
  Optimality.every_suffix_optimal Numerics.numericBounds first second splitPath

end NetHack.Sokoban41
