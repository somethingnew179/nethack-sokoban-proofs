/- Exact composition and optimal substructure for individual-move traces.
This is NOT a player-region quotient or push-graph compression theorem.
No correctness of an external searcher's state reduction is assumed.
-/
import NetHack.Sokoban.Model

namespace NetHack.Sokoban

theorem Trace.append {board : Board} {initial middle final : State}
    {first second : List Dir} {firstPushes firstMoves secondPushes secondMoves : Nat}
    (firstTrace : Trace board initial first middle firstPushes firstMoves)
    (secondTrace : Trace board middle second final secondPushes secondMoves) :
    Trace board initial (first ++ second) final
      (firstPushes + secondPushes) (firstMoves + secondMoves) := by
  induction firstTrace with
  | nil => simpa using secondTrace
  | cons head tail ih =>
    simpa [Nat.add_assoc] using Trace.cons head (ih secondTrace)

/-- Splitting the list of actual actions splits the logical trace and both
costs exactly; no abstract push-edge cost is substituted for walking. -/
theorem Trace.split {board : Board} {initial final : State}
    (first second : List Dir) {pushes moves : Nat}
    (whole : Trace board initial (first ++ second) final pushes moves) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace board initial first middle firstPushes firstMoves ∧
      Trace board middle second final secondPushes secondMoves ∧
      pushes = firstPushes + secondPushes ∧ moves = firstMoves + secondMoves := by
  induction first generalizing initial pushes moves with
  | nil =>
    exact ⟨initial, 0, 0, pushes, moves, Trace.nil initial, whole, by simp, by simp⟩
  | cons direction rest ih =>
    cases whole with
    | @cons state direction next rest final tailPushes tailMoves head tail =>
      rcases ih tail with ⟨middle, firstPushes, firstMoves, secondPushes, secondMoves,
        prefixTrace, suffixTrace, pushSum, moveSum⟩
      refine ⟨middle, next.pushCost + firstPushes, 1 + firstMoves, secondPushes, secondMoves,
        Trace.cons head prefixTrace, suffixTrace, ?_, ?_⟩ <;> omega

namespace Reduction

/-- A lower bound over ALL successful individual-move traces in the profile. -/
def PushLowerBound (board : Board) (initial : State) (cost : Nat) : Prop :=
  ∀ directions final pushes moves,
    Trace board initial directions final pushes moves → Goal final → cost ≤ pushes

/-- Any independently verified prefix transfers the initial lower bound to
the remaining problem. The prefix need not have been found optimally. -/
theorem continuation_lower_bound {board : Board} {initial middle : State}
    {prefixDirs : List Dir} {prefixPushes prefixMoves total : Nat}
    (lower : PushLowerBound board initial total)
    (prefixTrace : Trace board initial prefixDirs middle prefixPushes prefixMoves)
    {suffixDirs : List Dir} {final : State} {suffixPushes suffixMoves : Nat}
    (suffixTrace : Trace board middle suffixDirs final suffixPushes suffixMoves)
    (completed : Goal final) : total - prefixPushes ≤ suffixPushes := by
  have whole := prefixTrace.append suffixTrace
  have bound := lower _ _ _ _ whole completed
  omega

/-- A suffix of an attained globally optimal solution is itself optimal from
its actual reached state. The known suffix supplies the upper bound; the
initial universal lower bound supplies exclusion of every cheaper suffix. -/
theorem optimal_continuation_of_matching_cost {board : Board} {initial middle final : State}
    {prefixDirs suffixDirs : List Dir}
    {prefixPushes prefixMoves suffixPushes suffixMoves total : Nat}
    (lower : PushLowerBound board initial total)
    (prefixTrace : Trace board initial prefixDirs middle prefixPushes prefixMoves)
    (suffixTrace : Trace board middle suffixDirs final suffixPushes suffixMoves)
    (completed : Goal final) (matchingCost : total = prefixPushes + suffixPushes) :
    Trace board middle suffixDirs final suffixPushes suffixMoves ∧ Goal final ∧
    (∀ otherDirs otherFinal otherPushes otherMoves,
      Trace board middle otherDirs otherFinal otherPushes otherMoves →
      Goal otherFinal → suffixPushes ≤ otherPushes) := by
  refine ⟨suffixTrace, completed, ?_⟩
  intro otherDirs otherFinal otherPushes otherMoves alternative alternativeGoal
  have bound := continuation_lower_bound lower prefixTrace alternative alternativeGoal
  omega

/-- The corresponding statement for a better prefix reaching exactly the
same encoded state follows by appending the known successful suffix. -/
theorem prefix_minimal_of_matching_cost {board : Board} {initial middle final : State}
    {prefixDirs suffixDirs : List Dir}
    {prefixPushes prefixMoves suffixPushes suffixMoves total : Nat}
    (lower : PushLowerBound board initial total)
    (prefixTrace : Trace board initial prefixDirs middle prefixPushes prefixMoves)
    (suffixTrace : Trace board middle suffixDirs final suffixPushes suffixMoves)
    (completed : Goal final) (matchingCost : total = prefixPushes + suffixPushes)
    {otherDirs : List Dir} {otherPushes otherMoves : Nat}
    (alternative : Trace board initial otherDirs middle otherPushes otherMoves) :
    prefixPushes ≤ otherPushes := by
  have whole := alternative.append suffixTrace
  have bound := lower _ _ _ _ whole completed
  omega

/-- Every split of an attained optimal individual-move path yields an optimal
continuation from its genuinely reached full state. This quantifies over all
prefix lengths rather than checking one specially chosen suffix. -/
theorem every_suffix_optimal {board : Board} {initial final : State}
    (first second : List Dir) {total moves : Nat}
    (lower : PushLowerBound board initial total)
    (whole : Trace board initial (first ++ second) final total moves)
    (completed : Goal final) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace board initial first middle firstPushes firstMoves ∧
      Trace board middle second final secondPushes secondMoves ∧
      total = firstPushes + secondPushes ∧ moves = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace board middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) := by
  rcases whole.split first second with ⟨middle, firstPushes, firstMoves, secondPushes, secondMoves,
    prefixTrace, suffixTrace, pushSum, moveSum⟩
  have optimal := optimal_continuation_of_matching_cost lower prefixTrace suffixTrace completed pushSum
  exact ⟨middle, firstPushes, firstMoves, secondPushes, secondMoves,
    prefixTrace, suffixTrace, pushSum, moveSum, optimal.2.2⟩

end Reduction
end NetHack.Sokoban
