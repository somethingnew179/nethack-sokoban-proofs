/- Final mathematical glue for the source soko4-2 pattern certificate.
Finite checker premises remain explicit in this reusable module; the closed
optimality theorem instantiates them with actual kernel-checked certificates. -/
import NetHack.Sokoban.PatternProjection
import NetHack.Sokoban.Generated.Soko42Solution

namespace NetHack.Sokoban.PatternOptimality

open LowerBounds Generated

def value (state : State) : Int :=
  soko4_2Potential.value state + PatternCertificate.bonusOfBoxes state.boulders -
    NonlinearFacts.massPenalty state

def GoalChecks : Prop := ∀ pattern : PatternCertificate.Nine,
  PatternCertificate.bonus pattern ≤
    weightSum PatternCertificate.debt (PatternCertificate.occupied pattern) +
      max 0 (Int.ofNat (PatternCertificate.occupied pattern).length - 2)

theorem weightSum_neg (weight : Cell → Int) (cells : List Cell) :
    weightSum (fun cell => -weight cell) cells = -weightSum weight cells := by
  induction cells with
  | nil => simp [weightSum]
  | cons head tail ih =>
    simp only [weightSum, ih]
    omega

theorem debt_nonnegative (cell : Cell) : 0 ≤ PatternCertificate.debt cell := by
  have bound := soko4_2_potential_valid.nonpositive cell
  unfold PatternCertificate.debt
  omega

theorem goalBound (checked : GoalChecks) (state : State) (completed : Goal state) :
    value state ≤ 0 := by
  have certified := checked (PatternCertificate.ofBoxes state.boulders)
  rw [PatternProjection.occupied_ofBoxes] at certified
  have unique : PatternCertificate.support.Nodup := by decide
  have selectedDebt := NonlinearFacts.occupied_weightSum_le PatternCertificate.debt
    PatternCertificate.support state.boulders debt_nonnegative unique
  have selectedCount := NonlinearFacts.occupied_length_le PatternCertificate.support
    state.boulders unique
  have penalties :
      max (0 : Int) (Int.ofNat (NonlinearFacts.occupied PatternCertificate.support state.boulders).length - 2) ≤
        max 0 (Int.ofNat state.boulders.length - 2) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have debts : weightSum PatternCertificate.debt state.boulders =
      -weightSum soko4_2Potential.boulder state.boulders := by
    exact weightSum_neg soko4_2Potential.boulder state.boulders
  unfold Goal at completed
  unfold value Potential.value NonlinearFacts.massPenalty NonlinearFacts.massPenaltyWith
    NonlinearFacts.surplus PatternCertificate.bonusOfBoxes
  simp only [completed, List.length_nil, weightSum, Int.ofNat_eq_natCast] at certified penalties ⊢
  omega

theorem stepBound (numeric : PatternProjection.LocalBounds) : StepBound soko4_2.board value := by
  intro state direction transition checked
  have mass := NonlinearFacts.step_massPenalty soko4_2.board state direction transition checked
  have clear := step_player_clear soko4_2.board state direction transition checked
  rcases step_cases_full soko4_2.board state direction transition checked with walk | push
  · rcases walk with ⟨target, adjacent, floor, clearBox, clearHole, exactTransition⟩
    subst transition
    simp [value, Potential.value, Transition.pushCost, NonlinearFacts.massPenalty,
      NonlinearFacts.massPenaltyWith, NonlinearFacts.surplus, Int.ofNat_eq_natCast]
  · rcases push with ⟨source, result, adjacent, sourceFloor, member, pushed, exactTransition⟩
    have bonus := PatternProjection.bonus_push_bounds numeric state source direction result
      clear.1 clear.2.2.1 sourceFloor adjacent pushed
    have shape := (pushBoulder_spec soko4_2.board state source direction result pushed).1
    have erasedBox := weightSum_erase soko4_2Potential.boulder state.boulders source member
    subst transition
    rcases shape with stays | consumes
    · rcases stays with ⟨filled, boxes⟩
      have bonusBound := bonus.1
      simp only [value, Potential.value, Transition.pushCost, if_true,
        filled, afterFill, boxes, weightSum, Int.ofNat_eq_natCast] at mass ⊢
      omega
    · rcases consumes with ⟨filled, present, boxes⟩
      have erasedHole := weightSum_erase soko4_2Potential.hole state.holes result.landing present
      have bonusBound := bonus.2
      simp only [value, Potential.value, Transition.pushCost, if_true,
        filled, afterFill, boxes, Int.ofNat_eq_natCast] at mass ⊢
      omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem initial_value : value soko4_2.initial = 85 := by decide

theorem pushes_lower_bound (numeric : PatternProjection.LocalBounds) (goals : GoalChecks)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board soko4_2.initial directions final pushes moves)
    (completed : Goal final) : 85 ≤ pushes :=
  pushes_minimal_of_potential (stepBound numeric) (goalBound goals) 85 initial_value trace completed

theorem optimal_solution (numeric : PatternProjection.LocalBounds) (goals : GoalChecks) :
    Trace soko4_2.board soko4_2.initial soko4_2CandidatePath soko4_2CandidateFinalState 85 332 ∧
    Goal soko4_2CandidateFinalState ∧
    (∀ directions final pushes moves,
      Trace soko4_2.board soko4_2.initial directions final pushes moves →
      Goal final → 85 ≤ pushes) :=
  ⟨soko4_2_candidate_trace, soko4_2_candidate_goal,
    fun _ _ _ _ trace completed => pushes_lower_bound numeric goals trace completed⟩

end NetHack.Sokoban.PatternOptimality
