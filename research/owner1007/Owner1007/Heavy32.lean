import Owner1007.TokenPersistence
import NetHack.Sokoban.Reduction
import NetHack.Soko32Penalty5.ActionFacts

namespace Owner1007.Heavy32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection Owner1007.TokenAccounting

abbrev p := Generated.soko3_2Potential
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def ss (r : NetHack.Soko32SAT.Frames.Stay) : Int :=
  1 + p.boulder r.landing - p.boulder r.source

theorem pos_even : ∀ r ∈ NetHack.Soko32SAT.Frames.stays,
    p.boulder r.source < 0 → p.boulder r.landing < 0 → ss r % 2 = 0 := by decide +kernel

theorem covered_head {state : State} {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    {dir : Dir} {t : Transition} (checked : step soko3_2.board state dir = some t)
    {source : Cell} {result : Ending} (effect : Matches state t (.push source result)) :
    ∃ phase, phase < 12 ∧ NetHack.Soko32SAT.Frames.Covered phase state.player source dir result := by
  have pushed : t.pushed = true := by
    cases result with
    | stay landing => simp only [effect.2]
    | fill hole => simp only [effect.2.2]
  rcases step_cases_full soko3_2.board state dir t checked with walked | pushedCase
  · obtain ⟨target, _, _, _, _, shape⟩ := walked
    simp only [shape] at pushed
    contradiction
  · obtain ⟨other, res, adjacent, _, present, push, shape⟩ := pushedCase
    obtain ⟨phase, third, res2, active, _, adjacent2, push2, _, covered⟩ :=
      NetHack.Soko32SAT.Frames.original_push_covered reached dir t checked pushed
    have sourceEq := Option.some.inj (adjacent.symm.trans adjacent2)
    subst third
    have resultEq := Option.some.inj (push.symm.trans push2)
    subst res2
    have actual : Matches state t (.push other (ending res)) := by
      rcases (pushBoulder_spec soko3_2.board state other dir res push).1 with stay | fill
      · obtain ⟨unfilled, boxes⟩ := stay
        have actualStay : Matches state t (.push other (.stay res.landing)) :=
          ⟨present, by simpa only [unfilled, boxes, afterFill] using shape⟩
        simpa only [ending, unfilled] using actualStay
      · obtain ⟨filled, hazard, boxes⟩ := fill
        have actualFill : Matches state t (.push other (.fill res.landing)) :=
          ⟨present, hazard, by simpa only [filled, boxes, afterFill] using shape⟩
        simpa only [ending, filled] using actualFill
    have same := matches_unique state t (.push other (ending res)) (.push source result) actual effect
    obtain ⟨srcEq, endEq⟩ := Outcome.push.inj same
    rw [srcEq, endEq] at covered
    exact ⟨phase, active, covered⟩

theorem ownSlack_empty (potential : Potential) (outcomes : List Outcome) :
    ownSlack potential [] outcomes = 0 := by
  induction outcomes with
  | nil => rfl
  | cons outcome rest ih =>
    cases outcome with
    | walk target => simpa only [ownSlack, projectedOutcome, slack, update, Int.zero_add] using ih
    | push source result =>
      simpa only [ownSlack, projectedOutcome, update, move, List.not_mem_nil, if_false, slack, Int.zero_add] using ih

/-- A token whose whole slack budget is smaller than its current debt never
reaches debt0 before consumption; all its remaining slack is therefore even.
The recursive inequality avoids enumerating possible trajectories. -/
theorem cheap_token_even {state final : State} {dirs : List Dir} {pushes moves : Nat}
    {outcomes : List Outcome}
    (logged : Logged soko3_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (cell : Cell) (cheap : ownSlack p [cell] outcomes < -p.boulder cell) :
    ownSlack p [cell] outcomes % 2 = 0 := by
  induction logged generalizing history past pastMoves cell with
  | nil current => rfl
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    cases outcome with
    | walk target =>
      have smaller : ownSlack p [cell] outcomes < -p.boulder cell := by
        simpa only [ownSlack, projectedOutcome, slack, update, Int.zero_add] using cheap
      simpa only [ownSlack, projectedOutcome, slack, update, Int.zero_add] using ih nextReached cell smaller
    | push source result =>
      by_cases own : source = cell
      · subst source
        cases result with
        | stay landing =>
          have total : ownSlack p [cell] (.push cell (.stay landing) :: outcomes) =
              (1 + p.boulder landing - p.boulder cell) + ownSlack p [landing] outcomes := by
            simp [ownSlack, projectedOutcome, update, move, post, slack]
          have nextNN := tail.ownSlack_nonnegative Generated.soko3_2_potential_valid [landing]
          change 0 ≤ ownSlack p [landing] outcomes at nextNN
          have firstNN := logged_step_slack_nonnegative Generated.soko3_2_potential_valid head effect
          change 0 ≤ 1 + p.boulder landing - p.boulder cell at firstNN
          have posCell : p.boulder cell < 0 := by rw [total] at cheap; omega
          have posLanding : p.boulder landing < 0 := by rw [total] at cheap; omega
          have smaller : ownSlack p [landing] outcomes < -p.boulder landing := by
            rw [total] at cheap
            omega
          have restEven := ih nextReached landing smaller
          obtain ⟨phase, active, covered⟩ := covered_head reached head effect
          obtain ⟨row, member, _, sourceEq, _, landingEq⟩ := covered
          have rowEven := pos_even row member (by simpa only [sourceEq] using posCell)
            (by simpa only [landingEq] using posLanding)
          have firstEven : (1 + p.boulder landing - p.boulder cell) % 2 = 0 := by
            simpa only [ss, sourceEq, landingEq] using rowEven
          rw [total]
          omega
        | fill hole =>
          obtain ⟨phase, active, covered⟩ := covered_head reached head effect
          obtain ⟨_, sourceEq, _, holeEq⟩ := covered
          have fillZero := NetHack.Soko32Penalty5.fill_cost ⟨phase, active⟩
          have firstZero : slack p (.push cell (.fill hole)) = 0 := by
            simpa only [slack, sourceEq, holeEq] using fillZero.symm
          simp only [ownSlack, projectedOutcome, List.mem_cons, List.not_mem_nil, or_false,
            if_true, slack, update, move, post, List.erase_cons_head]
          change (slack p (.push cell (.fill hole)) + ownSlack p [] outcomes) % 2 = 0
          rw [firstZero, ownSlack_empty]
          rfl
      · have absent : source ∉ [cell] := by simp [own]
        have smaller : ownSlack p [cell] outcomes < -p.boulder cell := by
          simpa only [ownSlack, projectedOutcome, update, move, if_neg absent, slack, Int.zero_add] using cheap
        simpa only [ownSlack, projectedOutcome, update, move, if_neg absent, slack, Int.zero_add]
          using ih nextReached cell smaller

#print axioms cheap_token_even
end Owner1007.Heavy32
