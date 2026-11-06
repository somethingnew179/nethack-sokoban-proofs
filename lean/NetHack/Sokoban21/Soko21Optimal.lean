/- Exact push optimum for the complete real soko2-1 source map, canonical orientation.
Goal is all 10 original HOLEs filled. Upstairs travel through the locked door
is excluded, as are full-game actions beyond the frozen deterministic
rolling/no-collision pure puzzle profile.
The 475 individual moves of the witness are not asserted moves-minimal. -/
import NetHack.Sokoban21.Numerics
namespace NetHack.Sokoban21
open NetHack.Sokoban
open Generated

theorem soko2_1_pushes_optimal :
    Trace soko2_1.board soko2_1.initial soko2_1CandidatePath soko2_1CandidateFinalState 109 475 ∧
    Goal soko2_1CandidateFinalState ∧
    (∀ directions final pushes moves,
      Trace soko2_1.board soko2_1.initial directions final pushes moves → Goal final → 109 ≤ pushes) :=
  Optimality.optimal Numerics.numericBounds

theorem soko2_1_pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_1.board soko2_1.initial directions final pushes moves) (completed : Goal final) :
    109 ≤ pushes := Optimality.lower_bound Numerics.numericBounds trace completed

/-- A lower bound on individual moves, not a claim that 475 is minimal. -/
theorem soko2_1_moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_1.board soko2_1.initial directions final pushes moves) (completed : Goal final) :
    109 ≤ moves := Optimality.moves_lower_bound Numerics.numericBounds trace completed

theorem soko2_1_every_suffix_optimal (first second : List Dir)
    (splitPath : first ++ second = soko2_1CandidatePath) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace soko2_1.board soko2_1.initial first middle firstPushes firstMoves ∧
      Trace soko2_1.board middle second soko2_1CandidateFinalState secondPushes secondMoves ∧
      109 = firstPushes + secondPushes ∧ 475 = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace soko2_1.board middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) :=
  Optimality.every_suffix_optimal Numerics.numericBounds first second splitPath

end NetHack.Sokoban21
