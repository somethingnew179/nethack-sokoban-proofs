/- Actual legal-action premises imply the finite numeric guards. Projection
is exact for the relevant cells and conservative only for corner obstacles. -/
import NetHack.Sokoban41.Projection
import NetHack.Sokoban41.Rows

namespace NetHack.Sokoban41.GuardProjection
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
    blocked soko4_1.board state cell = true := by
  rcases Bool.or_eq_true_iff.mp relaxed with wall | box
  · exact Bool.or_eq_true_iff.mpr (Or.inl wall)
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (List.contains_iff_mem.mpr ((known_ofBoxes_true state.boulders cell).mp box).2))

private theorem relaxedSide_imp (state : State) (direction : Dir)
    (relaxed : relaxedSide (ofBoxes state.boulders) state.player direction = true) :
    sideBlocked soko4_1.board state direction = true := by
  cases adjacent : advance soko4_1.board state.player direction with
  | none => simp only [sideBlocked, adjacent]
  | some cell =>
    simp only [relaxedSide, adjacent] at relaxed
    simpa only [sideBlocked, adjacent] using relaxedBlocked_imp state cell relaxed

theorem relaxedCorner_imp (state : State) (direction : Dir)
    (relaxed : relaxedCorner (ofBoxes state.boulders) state.player direction = true) :
    cornerBlocked soko4_1.board state direction = true := by
  rcases Bool.and_eq_true_iff.mp relaxed with ⟨left, second⟩
  rcases Bool.and_eq_true_iff.mp left with ⟨diagonal, first⟩
  rw [corner_eq]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨diagonal, relaxedSide_imp state _ first⟩, relaxedSide_imp state _ second⟩

theorem relaxedCorner_clear (state : State) (direction : Dir)
    (clear : cornerBlocked soko4_1.board state direction = false) :
    relaxedCorner (ofBoxes state.boulders) state.player direction = false := by
  cases relaxed : relaxedCorner (ofBoxes state.boulders) state.player direction with
  | false => rfl
  | true => have blocked := relaxedCorner_imp state direction relaxed; simp [clear] at blocked

theorem budget_guard (boxes : List Cell) : budgetGuard (deadCount boxes) (ofBoxes boxes) = true := by
  by_cases zero : deadCount boxes = 0
  · have clear : known (ofBoxes boxes) 53 = false := by
      apply Bool.eq_false_iff.mpr
      intro present
      have box := ((known_ofBoxes_true boxes 53).mp present).2
      have budget := source_dead_budget boxes 53 box (by decide)
      omega
    simp [budgetGuard, zero, clear]
  · simp [budgetGuard, zero]

theorem walk_guard (state : State) (target : Cell) (direction : Dir)
    (playerClear : state.player ∉ state.boulders) (targetClear : target ∉ state.boulders)
    (cornerClear : cornerBlocked soko4_1.board state direction = false) :
    walkGuard ⟨state.player,target,direction⟩ (deadCount state.boulders) (ofBoxes state.boulders) = true := by
  have player := known_clear state.boulders state.player playerClear
  have target := known_clear state.boulders target targetClear
  have corner := relaxedCorner_clear state direction cornerClear
  simp only [walkGuard, budget_guard, player, target, corner, Bool.not_false, Bool.true_and]

theorem step_walk_guard (state : State) (direction : Dir) (transition : Transition)
    (checked : step soko4_1.board state direction = some transition)
    (target : Cell) (targetClear : target ∉ state.boulders) :
    walkGuard ⟨state.player,target,direction⟩ (deadCount state.boulders) (ofBoxes state.boulders) = true :=
  walk_guard state target direction (step_player_clear _ _ _ _ checked).2.2.1 targetClear
    (step_corner_clear _ _ _ _ checked)

private theorem two_dead_budget (boxes : List Cell) (first second : Cell)
    (firstPresent : first ∈ boxes) (secondPresent : second ∈ boxes)
    (firstDead : first ∈ deadCells) (secondDead : second ∈ deadCells)
    (different : first ≠ second) : 2 ≤ deadCount boxes := by
  have unique : [first,second].Nodup := by simp [different]
  have subset : [first,second] ⊆ boxes.filter (fun cell => deadCells.contains cell) := by
    intro cell member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst cell; simp [firstPresent, firstDead]
    · subst cell; simp [secondPresent, secondDead]
  exact List.Nodup.length_le_of_subset unique subset

theorem source_dead_guard (boxes : List Cell) (source : Cell) (present : source ∈ boxes)
    (limited : deadCount boxes ≤ 1) :
    (!deadCells.contains source || (decide (0 < deadCount boxes) &&
      (support.contains source || !known (ofBoxes boxes) 53))) = true := by
  by_cases dead : source ∈ deadCells
  · have budget := source_dead_budget boxes source present dead
    have positive : 0 < deadCount boxes := by omega
    by_cases supported : source ∈ support
    · simp [dead, positive, supported]
    · have clear : known (ofBoxes boxes) 53 = false := by
        apply Bool.eq_false_iff.mpr
        intro occupied
        have second := ((known_ofBoxes_true boxes 53).mp occupied).2
        have different : source ≠ 53 := by
          intro same
          subst source
          exact supported (by decide)
        have budget := two_dead_budget boxes source 53 present second dead (by decide) different
        omega
      simp [dead, positive, supported, clear]
  · simp [dead]

theorem push_guard (state : State) (edge : PushEdge) (result : PushResult)
    (limited : deadCount state.boulders ≤ 1)
    (playerEq : edge.player = state.player) (playerClear : state.player ∉ state.boulders)
    (present : edge.source ∈ state.boulders)
    (firstAdjacent : advance soko4_1.board edge.source edge.direction = some edge.first)
    (landingEq : edge.landing = result.landing)
    (sourceDead : edge.sourceDead = deadCells.contains edge.source)
    (checked : pushBoulder soko4_1.board state edge.source edge.direction = some result) :
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
  have deadGuard := source_dead_guard state.boulders edge.source present limited
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

end NetHack.Sokoban41.GuardProjection
