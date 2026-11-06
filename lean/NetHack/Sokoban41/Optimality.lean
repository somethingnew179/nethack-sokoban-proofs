/- Mathematical closure of the staged soko4-1 certificate.
All finite numeric obligations are explicit fields of NumericBounds. The
closed certificate instantiation is separate; no external solver is assumed. -/
import NetHack.Sokoban41.Geometry
import NetHack.Sokoban41.Facts
import NetHack.Sokoban41.GuardProjection
import NetHack.Sokoban.Generated.Soko41Solution
import NetHack.Sokoban.Reduction

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban41.Optimality
open NetHack.Sokoban
open LowerBounds Generated Projection

structure NumericBounds : Prop where
  walk_bounds : ∀ edge, edge ∈ walkEdges → ∀ dead, dead ≤ 1 → WalkBound edge dead
  push_bounds : ∀ edge, edge ∈ pushEdges → ∀ dead, dead ≤ 1 → PushBound edge dead
  consume_bounds : ∀ edge, edge ∈ pushEdges → ∀ dead, dead ≤ 1 →
    edge.landing ∈ soko4_1.initial.holes → edge.sourceDead = false → ConsumeBound edge dead
  bonus_range : ∀ dead player pattern, 0 ≤ bonus dead player pattern ∧ bonus dead player pattern ≤ 10
  goal_bound : ∀ dead player pattern, dead ≤ 1 → budgetGuard dead pattern = true →
    (Projection.occupied pattern).length ≤ 1 →
    dead + (support.filter (fun cell => known pattern cell && !deadCells.contains cell)).length ≤ 1 →
    bonus dead player pattern ≤ weightSum debt (Projection.occupied pattern)

def correction (state : State) : Int :=
  if Good state then bonus (deadCount state.boulders) state.player (ofBoxes state.boulders) else 0

def value (state : State) : Int := soko4_1Potential.value state + correction state

theorem bonus_full (dead player : Nat) (pattern : Ten) (spent : 2 ≤ dead) :
    bonus dead player pattern = 10 := by
  have zero : dead ≠ 0 := by omega
  have one : dead ≠ 1 := by omega
  simp only [bonus, if_neg zero, if_neg one]

theorem correction_nonnegative (numeric : NumericBounds) (state : State) : 0 ≤ correction state := by
  unfold correction
  split
  · exact (numeric.bonus_range _ _ _).1
  · exact Int.le_refl 0

theorem good_step_bound (numeric : NumericBounds) (state : State) (direction : Dir)
    (transition : Transition) (good : Good state)
    (checked : step soko4_1.board state direction = some transition) :
    soko4_1Potential.value state + bonus (deadCount state.boulders) state.player (ofBoxes state.boulders) ≤
      Int.ofNat transition.pushCost + soko4_1Potential.value transition.state +
        bonus (deadCount transition.state.boulders) transition.state.player (ofBoxes transition.state.boulders) := by
  by_cases limited : deadCount state.boulders ≤ 1
  · have clear := step_player_clear _ _ _ _ checked
    rcases step_cases_full _ _ _ _ checked with walk | pushed
    · rcases walk with ⟨target, adjacent, targetFloor, targetClear, _, shape⟩
      have member := walk_coverage state.player target direction clear.1 targetFloor adjacent
      have guard := GuardProjection.step_walk_guard state direction transition checked target targetClear
      have certified := numeric.walk_bounds _ member (deadCount state.boulders) limited
        (ofBoxes state.boulders) guard
      change bonus (deadCount state.boulders) state.player (ofBoxes state.boulders) ≤
        bonus (deadCount state.boulders) target (ofBoxes state.boulders) at certified
      subst transition
      simp only [Transition.pushCost, Bool.false_eq_true, ↓reduceIte, Int.ofNat_zero,
        Int.zero_add, Potential.value, Int.ofNat_eq_natCast] at *
      omega
    · rcases pushed with ⟨source, result, adjacent, sourceFloor, present, pushChecked, shape⟩
      have landingTarget := (pushBoulder_spec _ _ _ _ _ pushChecked).2
      rcases push_coverage state.player source direction result.landing clear.1 sourceFloor adjacent landingTarget with
        ⟨edge, member, playerEq, sourceEq, directionEq, landingEq⟩
      rcases push_facts edge member with
        ⟨_, firstAdjacent, moveSlack, consumeSlack, sourceDead, landingDead⟩
      have pushCheckedEdge : pushBoulder soko4_1.board state edge.source edge.direction = some result := by
        simpa only [sourceEq, directionEq] using pushChecked
      have edgePresent : edge.source ∈ state.boulders := by simpa only [sourceEq] using present
      have guard := GuardProjection.push_guard state edge result limited playerEq clear.2.2.1
        edgePresent firstAdjacent landingEq sourceDead pushCheckedEdge
      have erasedBox := weightSum_erase soko4_1Potential.boulder state.boulders source present
      rcases (pushBoulder_spec _ _ _ _ _ pushChecked).1 with stays | consumes
      · rcases stays with ⟨filled, boxes⟩
        have certified := numeric.push_bounds edge member (deadCount state.boulders) limited
          (ofBoxes state.boulders) guard
        have countEq : nextDead edge (deadCount state.boulders) = deadCount result.boulders := by
          rw [GuardProjection.nextDead_replace state.boulders edge edgePresent sourceDead landingDead]
          simp only [sourceEq, landingEq, boxes]
        have maskEq : ofBoxes result.boulders = change (ofBoxes state.boulders) (index source) (index result.landing) := by
          rw [boxes]
          exact ofBoxes_replace state.boulders good.1 source result.landing
        rw [countEq, playerEq, moveSlack, sourceEq, landingEq, ← maskEq] at certified
        subst transition
        simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_one, filled, afterFill, boxes,
          Potential.value, weightSum, Int.ofNat_eq_natCast] at certified ⊢
        omega
      · rcases consumes with ⟨filled, hazard, boxes⟩
        rcases push_consumes_deadCount state source direction result good.2.1 present pushChecked filled with
          ⟨sourceLive, counts⟩
        have original : edge.landing ∈ soko4_1.initial.holes := by
          rw [landingEq]
          exact good.2.1 hazard
        have live : edge.sourceDead = false := by
          rw [sourceDead, sourceEq]
          simpa using sourceLive
        have certified := numeric.consume_bounds edge member (deadCount state.boulders) limited original live
          (ofBoxes state.boulders) guard
        have maskEq : ofBoxes result.boulders = change (ofBoxes state.boulders) (index source) 10 := by
          rw [boxes]
          exact ofBoxes_erase state.boulders good.1 source
        rw [playerEq, consumeSlack, sourceEq, landingEq, ← maskEq] at certified
        have erasedHole := weightSum_erase soko4_1Potential.hole state.holes result.landing hazard
        subst transition
        simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_one, filled, afterFill,
          Potential.value, Int.ofNat_eq_natCast] at certified ⊢
        have erasedCounts : deadCount (state.boulders.erase source) = deadCount state.boulders := by
          simpa only [boxes] using counts
        simp only [boxes] at certified ⊢
        rw [erasedCounts]
        omega
  · have before : 2 ≤ deadCount state.boulders := by omega
    have monotone := step_deadCount state direction transition good checked
    have after : 2 ≤ deadCount transition.state.boulders := Nat.le_trans before monotone
    rw [bonus_full _ _ _ before, bonus_full _ _ _ after]
    have base := soko4_1_potential_valid.stepBound state direction transition checked
    omega

theorem stepBound (numeric : NumericBounds) : StepBound soko4_1.board value := by
  intro state direction transition checked
  by_cases good : Good state
  · have nextGood := step_good state direction transition good checked
    have bound := good_step_bound numeric state direction transition good checked
    simpa only [value, correction, if_pos good, if_pos nextGood, Int.add_assoc] using bound
  · have base := soko4_1_potential_valid.stepBound state direction transition checked
    have correction := correction_nonnegative numeric transition.state
    change soko4_1Potential.value state + Optimality.correction state ≤
      Int.ofNat transition.pushCost + (soko4_1Potential.value transition.state + Optimality.correction transition.state)
    rw [show Optimality.correction state = 0 by simp only [Optimality.correction, if_neg good]]
    omega

theorem debt_nonnegative (cell : Cell) : 0 ≤ debt cell := by
  have nonpositive := soko4_1_potential_valid.nonpositive cell
  unfold debt
  omega

private theorem debt_sum (boxes : List Cell) :
    weightSum debt boxes = -weightSum soko4_1Potential.boulder boxes := by
  induction boxes with
  | nil => rfl
  | cons head tail ih => simp only [weightSum, debt, ih]; omega

private theorem live_projection (boxes : List Cell) :
    support.filter (fun cell => known (ofBoxes boxes) cell && !deadCells.contains cell) = occupiedLive boxes := by
  unfold occupiedLive
  apply List.filter_congr
  intro cell member
  simp [known_ofBoxes_eq, member, Bool.and_comm]

theorem goalBound (numeric : NumericBounds) (state : State) (completed : Goal state) : value state ≤ 0 := by
  by_cases good : Good state
  · rcases goal_budgets state good completed with ⟨limited, total, live⟩
    have certified := numeric.goal_bound (deadCount state.boulders) state.player (ofBoxes state.boulders)
      limited (GuardProjection.budget_guard state.boulders) total (by simpa only [live_projection] using live)
    rw [occupied_ofBoxes] at certified
    have selected := NonlinearFacts.occupied_weightSum_le debt support state.boulders
      debt_nonnegative support_nodup
    have debts := debt_sum state.boulders
    change state.holes = [] at completed
    simp only [value, correction, if_pos good, Potential.value, completed, weightSum, Int.add_zero]
    omega
  · have base := soko4_1_potential_valid.goalBound state completed
    simpa only [value, correction, if_neg good, Int.add_zero] using base

theorem initial_value : value soko4_1.initial = 80 := by decide

theorem lower_bound (numeric : NumericBounds)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves) (completed : Goal final) :
    80 ≤ pushes :=
  pushes_minimal_of_potential (stepBound numeric) (goalBound numeric) 80 initial_value trace completed

theorem optimal (numeric : NumericBounds) :
    Trace soko4_1.board soko4_1.initial soko4_1CandidatePath soko4_1CandidateFinalState 80 299 ∧
    Goal soko4_1CandidateFinalState ∧
    (∀ directions final pushes moves,
      Trace soko4_1.board soko4_1.initial directions final pushes moves → Goal final → 80 ≤ pushes) :=
  ⟨soko4_1_candidate_trace, soko4_1_candidate_goal,
    fun _ _ _ _ trace completed => lower_bound numeric trace completed⟩


/-- Separate moves lower bound; the299-move witness is not claimed minimal. -/
theorem moves_lower_bound (numeric : NumericBounds)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves) (completed : Goal final) :
    80 ≤ moves := Nat.le_trans (lower_bound numeric trace completed) (trace_pushes_le_moves trace)

theorem every_suffix_optimal (numeric : NumericBounds) (first second : List Dir)
    (splitPath : first ++ second = soko4_1CandidatePath) :
    ∃ middle firstPushes firstMoves secondPushes secondMoves,
      Trace soko4_1.board soko4_1.initial first middle firstPushes firstMoves ∧
      Trace soko4_1.board middle second soko4_1CandidateFinalState secondPushes secondMoves ∧
      80 = firstPushes + secondPushes ∧ 299 = firstMoves + secondMoves ∧
      (∀ otherDirs otherFinal otherPushes otherMoves,
        Trace soko4_1.board middle otherDirs otherFinal otherPushes otherMoves →
        Goal otherFinal → secondPushes ≤ otherPushes) := by
  have whole : Trace soko4_1.board soko4_1.initial (first ++ second)
      soko4_1CandidateFinalState 80 299 := by
    rw [splitPath]
    exact soko4_1_candidate_trace
  exact Reduction.every_suffix_optimal first second
    (fun _ _ _ _ trace completed => lower_bound numeric trace completed) whole soko4_1_candidate_goal

end NetHack.Sokoban41.Optimality
