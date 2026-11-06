/- Actual legal-action premises imply the finite numeric guards. Projection
is exact for the relevant cells and conservative only for corner obstacles. -/
import NetHack.Sokoban21.Projection
import NetHack.Sokoban21.Rows

namespace NetHack.Sokoban21.GuardProjection
open NetHack.Sokoban
open Projection

private def rawCore (board : Board) (state : State) (direction : Dir) : Option Transition := do
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

theorem step_corner_clear (board : Board) (state : State) (direction : Dir) (transition : Transition)
    (checked : step board state direction = some transition) : cornerBlocked board state direction = false := by
  have core : rawCore board state direction = some transition := step_core_of _ _ _ _ checked
  cases corner : cornerBlocked board state direction with
  | false => rfl
  | true =>
    cases completed : goal state <;> cases adjacent : advance board state.player direction <;>
      simp [rawCore, corner, completed, adjacent] at core

private def sideBlocked (board : Board) (state : State) (direction : Dir) : Bool :=
  match advance board state.player direction with
  | none => true
  | some cell => blocked board state cell

private theorem corner_eq (board : Board) (state : State) (direction : Dir) :
    cornerBlocked board state direction =
      (direction.diagonal && sideBlocked board state direction.sides.1 && sideBlocked board state direction.sides.2) := rfl

theorem relaxedBlocked_imp (state : State) (cell : Cell)
    (relaxed : relaxedBlocked (ofBoxes state.boulders) cell = true) :
    blocked soko2_1.board state cell = true := by
  rcases Bool.or_eq_true_iff.mp relaxed with wall | box
  · exact Bool.or_eq_true_iff.mpr (Or.inl wall)
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (List.contains_iff_mem.mpr ((known_ofBoxes_true state.boulders cell).mp box).2))

private theorem relaxedSide_imp (state : State) (direction : Dir)
    (relaxed : relaxedSide (ofBoxes state.boulders) state.player direction = true) :
    sideBlocked soko2_1.board state direction = true := by
  cases adjacent : advance soko2_1.board state.player direction with
  | none => simp only [sideBlocked, adjacent]
  | some cell =>
    simp only [relaxedSide, adjacent] at relaxed
    simpa only [sideBlocked, adjacent] using relaxedBlocked_imp state cell relaxed

theorem relaxedCorner_imp (state : State) (direction : Dir)
    (relaxed : relaxedCorner (ofBoxes state.boulders) state.player direction = true) :
    cornerBlocked soko2_1.board state direction = true := by
  rcases Bool.and_eq_true_iff.mp relaxed with ⟨left, second⟩
  rcases Bool.and_eq_true_iff.mp left with ⟨diagonal, first⟩
  rw [corner_eq]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨diagonal, relaxedSide_imp state _ first⟩, relaxedSide_imp state _ second⟩

theorem relaxedCorner_clear (state : State) (direction : Dir)
    (clear : cornerBlocked soko2_1.board state direction = false) :
    relaxedCorner (ofBoxes state.boulders) state.player direction = false := by
  cases relaxed : relaxedCorner (ofBoxes state.boulders) state.player direction with
  | false => rfl
  | true => have blocked := relaxedCorner_imp state direction relaxed; simp [clear] at blocked

theorem budget_guard (boxes : List Cell) : budgetGuard (deadCount boxes) (ofBoxes boxes) = true := rfl

theorem walk_guard (state : State) (target : Cell) (direction : Dir)
    (playerClear : state.player ∉ state.boulders) (targetClear : target ∉ state.boulders)
    (cornerClear : cornerBlocked soko2_1.board state direction = false) :
    walkGuard ⟨state.player,target,direction⟩ (deadCount state.boulders) (ofBoxes state.boulders) = true := by
  have player := known_clear state.boulders state.player playerClear
  have target := known_clear state.boulders target targetClear
  have corner := relaxedCorner_clear state direction cornerClear
  simp only [walkGuard, budget_guard, player, target, corner, Bool.not_false, Bool.true_and]

theorem step_walk_guard (state : State) (direction : Dir) (transition : Transition)
    (checked : step soko2_1.board state direction = some transition)
    (target : Cell) (targetClear : target ∉ state.boulders) :
    walkGuard ⟨state.player,target,direction⟩ (deadCount state.boulders) (ofBoxes state.boulders) = true :=
  walk_guard state target direction (step_player_clear _ _ _ _ checked).2.2.1 targetClear
    (step_corner_clear _ _ _ _ checked)

theorem source_dead_guard (boxes : List Cell) (source : Cell) (present : source ∈ boxes) :
    (!deadCells.contains source || decide (0 < deadCount boxes)) = true := by
  by_cases dead : source ∈ deadCells
  · have budget := source_dead_budget boxes source present dead
    have positive : 0 < deadCount boxes := by omega
    simp [dead, positive]
  · simp [dead]

theorem push_guard (state : State) (edge : PushEdge) (result : PushResult)
    (_limited : deadCount state.boulders ≤ 3)
    (playerEq : edge.player = state.player) (playerClear : state.player ∉ state.boulders)
    (present : edge.source ∈ state.boulders)
    (firstAdjacent : advance soko2_1.board edge.source edge.direction = some edge.first)
    (landingEq : edge.landing = result.landing)
    (sourceDead : edge.sourceDead = deadCells.contains edge.source)
    (checked : pushBoulder soko2_1.board state edge.source edge.direction = some result) :
    pushGuard edge (deadCount state.boulders) (ofBoxes state.boulders) = true := by
  have player : known (ofBoxes state.boulders) edge.player = false := by
    rw [playerEq]
    exact known_clear state.boulders state.player playerClear
  have source : (!support.contains edge.source || known (ofBoxes state.boulders) edge.source) = true := by
    simp [known_ofBoxes_eq, present]
  rcases NonlinearFacts.pushBoulder_first_clear _ _ _ _ _ checked with
    ⟨first, adjacent, _, _, clear⟩
  have same : first = edge.first := Option.some.inj (adjacent.symm.trans firstAdjacent)
  have firstClear : known (ofBoxes state.boulders) edge.first = false := by
    rw [← same]
    exact known_clear state.boulders first clear
  have landing : (!known (ofBoxes state.boulders) edge.landing || decide (edge.landing = edge.source)) = true := by
    rcases NonlinearFacts.pushBoulder_landing_old_clear_or_source _ _ _ _ _ checked with equal | clear
    · simp [landingEq, equal]
    · simp [landingEq, known_clear state.boulders result.landing clear]
  have deadGuard := source_dead_guard state.boulders edge.source present
  rw [← sourceDead] at deadGuard
  simp only [pushGuard, Bool.and_eq_true_iff]
  exact ⟨⟨⟨⟨⟨budget_guard state.boulders, by simp [player]⟩, source⟩,
    by simp [firstClear]⟩, landing⟩, deadGuard⟩

private theorem contains_toNat (cells : List Cell) (cell : Cell) :
    (cells.contains cell).toNat = if cell ∈ cells then 1 else 0 := by
  by_cases present : cell ∈ cells <;> simp [present]

theorem nextDead_replace (boxes : List Cell) (edge : PushEdge) (present : edge.source ∈ boxes)
    (sourceDead : edge.sourceDead = deadCells.contains edge.source)
    (landingDead : edge.landingDead = deadCells.contains edge.landing) :
    nextDead edge (deadCount boxes) = deadCount (edge.landing :: boxes.erase edge.source) := by
  rw [nextDead, sourceDead, landingDead, contains_toNat, contains_toNat]
  exact (deadCount_replace_exact boxes edge.source edge.landing present).symm

end NetHack.Sokoban21.GuardProjection
