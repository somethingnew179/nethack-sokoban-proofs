/- Logical isomorphisms for the exact individual-move Sokoban model.
All dynamic boulder/hazard lists are transformed, including rolling traps,
doors, diagonal corner rules, consumption and both declared costs. -/
import NetHack.Sokoban.Symmetry.Permutation

set_option linter.unusedSimpArgs false

namespace NetHack.Sokoban.Symmetry

structure DirectionPermutation where
  apply : Dir → Dir
  involutive : ∀ direction, apply (apply direction) = direction
  diagonal : ∀ direction, (apply direction).diagonal = direction.diagonal
  opposite : ∀ direction, (apply direction).opposite = apply direction.opposite
  sides : ∀ direction, direction.diagonal = true →
    (apply direction).sides = (apply direction.sides.1, apply direction.sides.2)

def mapBoard (perm : CellPermutation) (board : Board) : Board := {
  width := board.width
  height := board.height
  floor := board.floor.map perm.apply
  rollingTraps := board.rollingTraps.map perm.apply
  doors := board.doors.map perm.apply
  exit := perm.apply board.exit }

def mapState (perm : CellPermutation) (state : State) : State := {
  player := perm.apply state.player
  boulders := state.boulders.map perm.apply
  holes := state.holes.map perm.apply }

def mapPush (perm : CellPermutation) (result : PushResult) : PushResult := {
  boulders := result.boulders.map perm.apply
  filled := result.filled.map perm.apply
  landing := perm.apply result.landing }

def mapTransition (perm : CellPermutation) (transition : Transition) : Transition := {
  state := mapState perm transition.state
  pushed := transition.pushed
  filled := transition.filled.map perm.apply
  pushSource := transition.pushSource.map perm.apply
  landing := transition.landing.map perm.apply }

@[simp] theorem state_player (perm : CellPermutation) (state : State) : (mapState perm state).player = perm.apply state.player := rfl
@[simp] theorem state_boulders (perm : CellPermutation) (state : State) : (mapState perm state).boulders = state.boulders.map perm.apply := rfl
@[simp] theorem state_holes (perm : CellPermutation) (state : State) : (mapState perm state).holes = state.holes.map perm.apply := rfl

@[simp] theorem board_width (perm : CellPermutation) (board : Board) : (mapBoard perm board).width = board.width := rfl
@[simp] theorem board_height (perm : CellPermutation) (board : Board) : (mapBoard perm board).height = board.height := rfl
@[simp] theorem board_floor (perm : CellPermutation) (board : Board) : (mapBoard perm board).floor = board.floor.map perm.apply := rfl
@[simp] theorem board_doors (perm : CellPermutation) (board : Board) : (mapBoard perm board).doors = board.doors.map perm.apply := rfl
@[simp] theorem board_rolling (perm : CellPermutation) (board : Board) : (mapBoard perm board).rollingTraps = board.rollingTraps.map perm.apply := rfl

theorem board_involutive (perm : CellPermutation) (board : Board) :
    mapBoard perm (mapBoard perm board) = board := by
  cases board
  simp [mapBoard, perm.list_involutive, perm.involutive]

theorem state_involutive (perm : CellPermutation) (state : State) :
    mapState perm (mapState perm state) = state := by
  cases state
  simp [mapState, perm.list_involutive, perm.involutive]

theorem option_involutive (perm : CellPermutation) (cell : Option Cell) :
    (cell.map perm.apply).map perm.apply = cell := by
  cases cell <;> simp [perm.involutive]

structure BoardIsomorphism (board : Board) where
  cells : CellPermutation
  directions : DirectionPermutation
  advance : ∀ cell direction,
    NetHack.Sokoban.advance (mapBoard cells board) (cells.apply cell) (directions.apply direction) =
      (NetHack.Sokoban.advance board cell direction).map cells.apply

namespace BoardIsomorphism

theorem blocked_map {board : Board} (iso : BoardIsomorphism board) (state : State) (cell : Cell) :
    blocked (mapBoard iso.cells board) (mapState iso.cells state) (iso.cells.apply cell) =
      blocked board state cell := by
  simp only [blocked, mapState, board_floor, board_doors, iso.cells.contains_map]

private def side (board : Board) (state : State) (direction : Dir) : Bool :=
  match NetHack.Sokoban.advance board state.player direction with
  | none => true
  | some cell => blocked board state cell

private theorem corner_eq (board : Board) (state : State) (direction : Dir) :
    cornerBlocked board state direction =
      (direction.diagonal && side board state direction.sides.1 && side board state direction.sides.2) := rfl

private theorem side_map {board : Board} (iso : BoardIsomorphism board) (state : State) (direction : Dir) :
    side (mapBoard iso.cells board) (mapState iso.cells state) (iso.directions.apply direction) =
      side board state direction := by
  unfold side
  change (match NetHack.Sokoban.advance (mapBoard iso.cells board) (iso.cells.apply state.player)
      (iso.directions.apply direction) with
    | none => true
    | some cell => blocked (mapBoard iso.cells board) (mapState iso.cells state) cell) = _
  rw [iso.advance]
  cases adjacent : NetHack.Sokoban.advance board state.player direction <;>
    simp [iso.blocked_map]

theorem corner_map {board : Board} (iso : BoardIsomorphism board) (state : State) (direction : Dir) :
    cornerBlocked (mapBoard iso.cells board) (mapState iso.cells state) (iso.directions.apply direction) =
      cornerBlocked board state direction := by
  rw [corner_eq, corner_eq, iso.directions.diagonal]
  cases diagonal : direction.diagonal with
  | false => simp
  | true =>
    rw [iso.directions.sides direction diagonal]
    simp only [Prod.fst, Prod.snd, iso.side_map]

theorem roll_map {board : Board} (iso : BoardIsomorphism board)
    (stationary holes : List Cell) (direction : Dir) (fuel current : Nat) :
    roll (mapBoard iso.cells board) (stationary.map iso.cells.apply) (holes.map iso.cells.apply)
      (iso.directions.apply direction) fuel (iso.cells.apply current) =
        (roll board stationary holes direction fuel current).map (mapPush iso.cells) := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    cases adjacent : NetHack.Sokoban.advance board current direction with
    | none => simp only [roll, iso.advance, adjacent, Option.map_none, Option.map_some, mapPush, List.map_cons]
    | some next =>
      cases door : board.doors.contains next <;>
        cases floor : board.floor.contains next <;>
        cases collision : stationary.contains next <;>
        cases hazard : holes.contains next <;>
        simp only [roll, iso.advance, adjacent, Option.map_some, board_floor, board_doors,
          iso.cells.contains_map, door, floor, collision, hazard, ih, mapPush,
          List.map_cons, List.map_nil, Option.map_none, Option.map_some, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem push_map {board : Board} (iso : BoardIsomorphism board) (state : State)
    (source : Cell) (direction : Dir) :
    pushBoulder (mapBoard iso.cells board) (mapState iso.cells state) (iso.cells.apply source)
      (iso.directions.apply direction) =
        (pushBoulder board state source direction).map (mapPush iso.cells) := by
  cases diagonal : direction.diagonal with
  | true => simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal]
  | false =>
    cases support : NetHack.Sokoban.advance board source direction.opposite with
    | none => simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal, support]
    | some behind =>
      cases supportBlocked : (!board.floor.contains behind || board.doors.contains behind) with
      | true => simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal, support, supportBlocked]
      | false =>
        cases adjacent : NetHack.Sokoban.advance board source direction with
        | none => simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal, support, supportBlocked, adjacent]
        | some destination =>
          cases blockedDestination : (!board.floor.contains destination || board.doors.contains destination || state.boulders.contains destination) with
          | true => simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal, support, supportBlocked, adjacent, blockedDestination]
          | false =>
            cases hazard : state.holes.contains destination <;>
              cases rolling : board.rollingTraps.contains destination <;>
              simp only [bind, pure, pushBoulder, iso.directions.diagonal, iso.directions.opposite, iso.advance, mapState, board_floor, board_doors, board_rolling, board_width, board_height, iso.cells.contains_map, iso.cells.erase_map, Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, Bool.false_eq_true, ↓reduceIte, iso.roll_map, mapPush, List.map_cons, diagonal, support, supportBlocked, adjacent, blockedDestination, hazard, rolling]


private def core (board : Board) (state : State) (direction : Dir) : Option Transition := do
  if goal state then none else pure ()
  let target ← NetHack.Sokoban.advance board state.player direction
  if !board.floor.contains target || board.doors.contains target || cornerBlocked board state direction then
    none else pure ()
  if state.boulders.contains target then
    let pushed ← pushBoulder board state target direction
    return {state := {player := target, boulders := pushed.boulders, holes := afterFill state.holes pushed.filled}, pushed := true, filled := pushed.filled, pushSource := some target, landing := some pushed.landing}
  else
    if state.holes.contains target then none
    else return {state := {state with player := target}, pushed := false, filled := none}

private theorem step_eq (board : Board) (state : State) (direction : Dir) :
    step board state direction = (do
      if !standingAllowed board state then none else pure ()
      core board state direction) := rfl

theorem standing_map {board : Board} (iso : BoardIsomorphism board) (state : State) :
    standingAllowed (mapBoard iso.cells board) (mapState iso.cells state) =
      standingAllowed board state := by
  simp only [standingAllowed, mapState, board_floor, board_doors, iso.cells.contains_map]

theorem goal_map (perm : CellPermutation) (state : State) :
    goal (mapState perm state) = goal state := by
  change (state.holes.map perm.apply).isEmpty = state.holes.isEmpty
  cases state.holes <;> rfl

theorem afterFill_map (perm : CellPermutation) (holes : List Cell) (filled : Option Cell) :
    afterFill (holes.map perm.apply) (filled.map perm.apply) =
      (afterFill holes filled).map perm.apply := by
  cases filled <;> simp only [afterFill, Option.map_none, Option.map_some, perm.erase_map]

private theorem core_map {board : Board} (iso : BoardIsomorphism board) (state : State)
    (direction : Dir) :
    core (mapBoard iso.cells board) (mapState iso.cells state) (iso.directions.apply direction) =
      (core board state direction).map (mapTransition iso.cells) := by
  cases completed : goal state with
  | true => simp only [core, goal_map, completed, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.map_none] <;> rfl
  | false =>
    cases adjacent : NetHack.Sokoban.advance board state.player direction with
    | none => simp only [core, goal_map, completed, state_player, state_boulders, state_holes, iso.advance, adjacent, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, Option.map_none] <;> rfl
    | some target =>
      cases blockedTarget : (!board.floor.contains target || board.doors.contains target || cornerBlocked board state direction) with
      | true => simp only [core, goal_map, completed, state_player, state_boulders, state_holes, iso.advance, adjacent, board_floor, board_doors, iso.cells.contains_map, iso.corner_map, blockedTarget, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some] <;> rfl
      | false =>
        cases box : state.boulders.contains target with
        | true =>
          cases pushed : pushBoulder board state target direction with
          | none => simp only [core, goal_map, completed, state_player, state_boulders, state_holes, iso.advance, adjacent, board_floor, board_doors, iso.cells.contains_map, iso.corner_map, blockedTarget, box, iso.push_map, pushed, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some] <;> rfl
          | some result => simp only [core, goal_map, completed, state_player, state_boulders, state_holes, iso.advance, adjacent, board_floor, board_doors, iso.cells.contains_map, iso.corner_map, blockedTarget, box, iso.push_map, pushed, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some, mapPush, mapTransition, afterFill_map] <;> rfl
        | false =>
          cases hazard : state.holes.contains target <;>
            simp only [core, goal_map, completed, state_player, state_boulders, state_holes, iso.advance, adjacent, board_floor, board_doors, iso.cells.contains_map, iso.corner_map, blockedTarget, box, hazard, bind, pure, Bool.false_eq_true, ↓reduceIte, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some, mapTransition] <;> rfl


theorem step_map {board : Board} (iso : BoardIsomorphism board) (state : State)
    (direction : Dir) :
    step (mapBoard iso.cells board) (mapState iso.cells state) (iso.directions.apply direction) =
      (step board state direction).map (mapTransition iso.cells) := by
  rw [step_eq, step_eq, iso.standing_map]
  cases standing : standingAllowed board state <;>
    simp only [standing, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, pure, Option.bind_none, Option.bind_some, Option.map_none, iso.core_map]

end BoardIsomorphism
end NetHack.Sokoban.Symmetry
