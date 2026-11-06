/- Algebraic single-charge rule. The group disjointness still has to be
transported from the original partition along actual Model transitions. -/
import NetHack.Sokoban.RawGhostBonus
namespace NetHack.Sokoban.DisjointSlack
open HazardPattern GhostProjection LowerBounds

theorem sum_bound (potential : Potential) (first second : List Cell)
    (separate : ∀ c ∈ first, c ∉ second) (outcome : Outcome)
    (nonnegative : 0 ≤ slack potential outcome) :
    slack potential (projectedOutcome first outcome) +
      slack potential (projectedOutcome second outcome) ≤ slack potential outcome := by
  cases outcome with
  | walk target => exact Int.le_refl _
  | push source result =>
    by_cases one : source ∈ first
    · have two : source ∉ second := separate source one
      simp only [projectedOutcome,if_pos one,if_neg two,slack,Int.add_zero]
      cases result <;> exact Int.le_refl _
    · by_cases two : source ∈ second
      · simp only [projectedOutcome,if_neg one,if_pos two,slack,Int.zero_add]
        cases result <;> exact Int.le_refl _
      · simpa only [projectedOutcome,if_neg one,if_neg two,slack,Int.zero_add] using nonnegative

end NetHack.Sokoban.DisjointSlack
