/- Completeness of the already used endpoint oracle on standing, non-goal
states with distinct boulders. The public expression below is definitionally
the original Model.step, not a different puzzle transition system. -/
import NetHack.Sokoban.GhostShadow

namespace NetHack.Sokoban.GhostProjection
open HazardPattern PatternCorrection
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def exposedStep (board : Board) (state : State) (direction : Dir) : Option Transition := do
  if !standingAllowed board state then none else pure ()
  if goal state then none else pure ()
  let target ← advance board state.player direction
  if !board.floor.contains target || board.doors.contains target || cornerBlocked board state direction then
    none else pure ()
  if state.boulders.contains target then
    let pushed ← pushBoulder board state target direction
    return {state := {player := target, boulders := pushed.boulders, holes := afterFill state.holes pushed.filled}, pushed := true, filled := pushed.filled, pushSource := some target, landing := some pushed.landing}
  else
    if state.holes.contains target then none
    else return {state := {state with player := target}, pushed := false, filled := none}

theorem exposedStep_eq (board : Board) (state : State) (direction : Dir) :
    exposedStep board state direction = step board state direction := by
  cases a : standingAllowed board state <;>
    simp only [exposedStep,step,a,Bool.not_true,Bool.not_false,Bool.false_eq_true,
      ↓reduceIte,bind,pure,Option.bind_some] <;> rfl

theorem oracle_decode_exact (board : Board) (state : State) (unique : state.boulders.Nodup)
    (standing : standingAllowed board state = true) (ongoing : goal state = false)
    (direction : Dir) :
    (step board state direction).map decode =
      stepOracle board (project state.boulders) (project state.holes) state.player direction := by
  have physical : state.player ∈ board.floor ∧ state.player ∉ board.doors ∧
      state.player ∉ state.boulders ∧ state.player ∉ state.holes := by
    simpa [standingAllowed,and_assoc] using standing
  have heroBox : project state.boulders state.player = false := by simp [project,physical.2.2.1]
  have heroHole : project state.holes state.player = false := by simp [project,physical.2.2.2]
  have cornerEq := corner_project board state direction
  rw [←exposedStep_eq]
  cases adjacent : advance board state.player direction with
  | none => simp [exposedStep,stepOracle,standing,ongoing,heroBox,heroHole,adjacent]
  | some target =>
    cases floor : board.floor.contains target <;>
      cases door : board.doors.contains target <;>
      cases corner : cornerBlocked board state direction <;>
      simp only [exposedStep,stepOracle,standing,ongoing,heroBox,heroHole,cornerEq,
        adjacent,floor,door,corner,Bool.not_true,Bool.not_false,Bool.false_or,Bool.true_or,
        Bool.false_eq_true,↓reduceIte,bind,pure,Option.bind_some,Option.map_none]
    all_goals first | rfl | skip
    cases box : state.boulders.contains target with
    | false =>
      have absent : target ∉ state.boulders := by simpa using box
      by_cases hole : target ∈ state.holes <;>
        simp [project,absent,hole,decode,Option.map_some]
    | true =>
      have present : target ∈ state.boulders := List.contains_iff_mem.mp box
      have endpoints := pushOracle_exact board state unique target direction
      cases pushed : pushBoulder board state target direction with
      | none =>
        simp only [pushed,Option.map_none,project] at endpoints
        simp [project,present,pushed,←endpoints]
      | some result =>
        simp only [pushed,Option.map_some] at endpoints
        rw [←endpoints]
        cases filled : result.filled <;>
          simp [project,present,pushed,decode,ending,filled]

/-- No proposer completeness premise: a successful oracle edge is realized
by the original executable Model under the explicitly proved state facts. -/
theorem oracle_realized (board : Board) (state : State) (unique : state.boulders.Nodup)
    (standing : standingAllowed board state = true) (ongoing : goal state = false)
    (direction : Dir) (outcome : Outcome)
    (oracle : stepOracle board (project state.boulders) (project state.holes) state.player direction =
      some outcome) :
    ∃ t, step board state direction = some t ∧ Matches state t outcome := by
  have correspondence := oracle_decode_exact board state unique standing ongoing direction
  rw [oracle] at correspondence
  cases actual : step board state direction with
  | none => simp [actual] at correspondence
  | some t =>
    rcases stepOracle_covers board state unique direction t actual with ⟨other,found,effect⟩
    have same : other = outcome := Option.some.inj (found.symm.trans oracle)
    exact ⟨t,rfl,same ▸ effect⟩

end NetHack.Sokoban.GhostProjection
