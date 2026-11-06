/- Closed pushes-optimality theorem for the complete pinned soko4-2 board.
The search proposer, heuristic and pruning rules are not premises. Every
finite inequality is checked by Lean and related to every admitted action.
The winning path has332moves; moves-optimality is deliberately a separate
property and is not asserted by this theorem. -/
import NetHack.Sokoban.PatternOptimality
import NetHack.Sokoban.PatternCertificate
import NetHack.Sokoban.Reduction

namespace NetHack.Sokoban.Soko42Optimal

theorem lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board soko4_2.initial directions final pushes moves)
    (completed : Goal final) : 85 ≤ pushes :=
  PatternOptimality.pushes_lower_bound PatternCertificate.local_bounds
    PatternCertificate.goal_pattern trace completed

/-- A separate lower bound for the separate moves metric. This does not
claim that the332-move witness minimizes moves. -/
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board soko4_2.initial directions final pushes moves)
    (completed : Goal final) : 85 ≤ moves :=
  Nat.le_trans (lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)

theorem optimal :
    Trace soko4_2.board soko4_2.initial Generated.soko4_2CandidatePath
      Generated.soko4_2CandidateFinalState 85 332 ∧
    Goal Generated.soko4_2CandidateFinalState ∧
    (∀ directions final pushes moves,
      Trace soko4_2.board soko4_2.initial directions final pushes moves →
      Goal final → 85 ≤ pushes) :=
  PatternOptimality.optimal_solution PatternCertificate.local_bounds PatternCertificate.goal_pattern

/-- Every prefix of this real winning path reaches a state from which the
remaining suffix is pushes-optimal. This is a cost-preserving trace argument,
not an assumed reduction to a push graph. -/
theorem every_suffix_optimal (first second : List Dir)
    (splitPath : first ++ second = Generated.soko4_2CandidatePath) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace soko4_2.board soko4_2.initial first middle firstPushes firstMoves ∧
      Trace soko4_2.board middle second Generated.soko4_2CandidateFinalState secondPushes secondMoves ∧
      85 = firstPushes + secondPushes ∧ 332 = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace soko4_2.board middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) := by
  have whole : Trace soko4_2.board soko4_2.initial (first ++ second)
      Generated.soko4_2CandidateFinalState 85 332 := by
    rw [splitPath]
    exact Generated.soko4_2_candidate_trace
  exact Reduction.every_suffix_optimal first second
    (fun _ _ _ _ trace completed => lower_bound trace completed) whole Generated.soko4_2_candidate_goal

end NetHack.Sokoban.Soko42Optimal
