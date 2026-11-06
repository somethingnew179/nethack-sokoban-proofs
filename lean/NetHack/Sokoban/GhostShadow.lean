/- Every successful Model step projects to a persistent group's walk or
own push. An untracked push becomes a zero-cost shadow walk; its actual
hazard erasure is handled separately by the proved phase invariant.
No claim of equality between shadow-graph distance and real moves is made. -/
import NetHack.Sokoban.GhostProjection

namespace NetHack.Sokoban.GhostProjection
open HazardPattern PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def projectedOutcome (group : List Cell) : Outcome → Outcome
  | .walk target => .walk target
  | .push source result => if source ∈ group then .push source result else .walk source

def decode (t : Transition) : Outcome :=
  if t.pushed then
    match t.filled with
    | some hole => .push (t.pushSource.getD 0) (.fill hole)
    | none => .push (t.pushSource.getD 0) (.stay (t.landing.getD 0))
  else .walk t.state.player

theorem matches_decode (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) : decode t = outcome := by
  cases outcome with
  | walk target => rw [effect]; rfl
  | push source result =>
    cases result with
    | stay landing => rw [effect.2]; rfl
    | fill hole => rw [effect.2.2]; rfl

theorem matches_unique (state : State) (t : Transition) (a b : Outcome)
    (left : Matches state t a) (right : Matches state t b) : a = b :=
  (matches_decode state t a left).symm.trans (matches_decode state t b right)

/-- This is coverage of all real transitions under a proved state invariant.
The disjointness premise follows from the existing original hazard phases;
it is not an extra premise on completing original-map Traces. -/
theorem original_step_shadow (board : Board) (state : State) (group : List Cell)
    (unique : state.boulders.Nodup) (subset : group ⊆ state.boulders)
    (disjoint : ∀ box ∈ state.boulders, box ∉ state.holes)
    (direction : Dir) (t : Transition) (checked : step board state direction = some t) :
    ∃ outcome, Matches state t outcome ∧
      stepOracle board (project group) (project state.holes) state.player direction =
        some (projectedOutcome group outcome) := by
  have standing := step_player_clear board state direction t checked
  have heroBox : project group state.player = false := by
    apply clear_of_subset (project group) (project state.boulders)
      (project_subset group state.boulders subset) state.player
    simp [project,standing.2.2.1]
  have heroHole : project state.holes state.player = false := by
    simp [project,standing.2.2.2]
  have clear := original_corner_projected board state group subset direction t checked
  rcases step_cases_full board state direction t checked with walked | pushed
  · rcases walked with ⟨target,adjacent,floor,boxClear,holeClear,shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t target adjacent checked
    have floorTrue : board.floor.contains target = true := List.contains_iff_mem.mpr floor
    have doorFalse : board.doors.contains target = false := by simp [door]
    have groupClear : project group target = false := by
      apply clear_of_subset _ _ (project_subset group state.boulders subset) target
      simp [project,boxClear]
    have holeFalse : project state.holes target = false := by simp [project,holeClear]
    refine ⟨.walk target,shape,?_⟩
    simp [stepOracle,projectedOutcome,heroBox,heroHole,adjacent,
      floor,door,floorTrue,doorFalse,clear,groupClear,holeFalse]
  · rcases pushed with ⟨source,result,adjacent,floor,present,push,shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t source adjacent checked
    have floorTrue : board.floor.contains source = true := List.contains_iff_mem.mpr floor
    have doorFalse : board.doors.contains source = false := by simp [door]
    have sourceHole : project state.holes source = false := by simp [project,disjoint source present]
    have endpoint := original_push_projected board state group subset unique source direction result push
    have produces : stepOracle board (project group) (project state.holes) state.player direction =
        some (projectedOutcome group (.push source (ending result))) := by
      by_cases owner : source ∈ group
      · have sourceTrue : project group source = true := List.contains_iff_mem.mpr owner
        simp [stepOracle,projectedOutcome,owner,heroBox,heroHole,adjacent,
          floor,door,floorTrue,doorFalse,clear,sourceTrue,endpoint]
      · have sourceFalse : project group source = false := by simp [project,owner]
        simp [stepOracle,projectedOutcome,owner,heroBox,heroHole,adjacent,
          floor,door,floorTrue,doorFalse,clear,sourceFalse,sourceHole]
    rcases (pushBoulder_spec board state source direction result push).1 with stay | fill
    · rcases stay with ⟨unfilled,boxes⟩
      refine ⟨.push source (.stay result.landing),⟨present,?_⟩,?_⟩
      · simpa only [unfilled,boxes,afterFill] using shape
      · simpa only [ending,unfilled] using produces
    · rcases fill with ⟨filled,hazard,boxes⟩
      refine ⟨.push source (.fill result.landing),⟨present,hazard,?_⟩,?_⟩
      · simpa only [filled,boxes,afterFill] using shape
      · simpa only [ending,filled] using produces

theorem original_matches_shadow (board : Board) (state : State) (group : List Cell)
    (unique : state.boulders.Nodup) (subset : group ⊆ state.boulders)
    (disjoint : ∀ box ∈ state.boulders, box ∉ state.holes)
    (direction : Dir) (t : Transition) (checked : step board state direction = some t)
    (outcome : Outcome) (effect : Matches state t outcome) :
    stepOracle board (project group) (project state.holes) state.player direction =
      some (projectedOutcome group outcome) := by
  rcases original_step_shadow board state group unique subset disjoint direction t checked with ⟨o,a,b⟩
  simpa only [matches_unique state t o outcome a effect] using b

end NetHack.Sokoban.GhostProjection
