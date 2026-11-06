/- NetHack 5.0 Sokoban: a finite, executable pure-puzzle profile.

Source boundary: no monsters, tools, teleportation, new traps/boulders, door
opening/breaking, or exotic locomotion. Walking into an unfilled pit/hole is
excluded. Rolling-boulder traps retain their real Sokoban sliding behaviour,
but a roll that would collide with another boulder or an intact door is
excluded: momentum transfer and stacked boulders belong to a later profile.
Every admitted transition displaces the hero once. Its push cost is one iff
it initiates a boulder push; an automatic roll can travel several cells.
Execution stops on the original completion condition: no original pit/hole
remains. Exit travel after Sokoban rules are lifted is a separate problem.
This module supplies semantics and checker soundness, not a C-refinement axiom.
-/
namespace NetHack.Sokoban

abbrev Cell := Nat

inductive Dir where
  | north | south | east | west
  | northEast | northWest | southEast | southWest
  deriving Repr, BEq, DecidableEq, Inhabited

def Dir.dx : Dir → Int
  | .east | .northEast | .southEast => 1
  | .west | .northWest | .southWest => -1
  | _ => 0

def Dir.dy : Dir → Int
  | .south | .southEast | .southWest => 1
  | .north | .northEast | .northWest => -1
  | _ => 0

def Dir.diagonal : Dir → Bool
  | .north | .south | .east | .west => false
  | _ => true

def Dir.sides : Dir → Dir × Dir
  | .northEast => (.north, .east)
  | .northWest => (.north, .west)
  | .southEast => (.south, .east)
  | .southWest => (.south, .west)
  | _ => (.north, .north)

def Dir.opposite : Dir → Dir
  | .north => .south
  | .south => .north
  | .east => .west
  | .west => .east
  | .northEast => .southWest
  | .northWest => .southEast
  | .southEast => .northWest
  | .southWest => .northEast

def cardinalDirs : List Dir := [.north, .south, .east, .west]
def allDirs : List Dir := cardinalDirs ++ [.northEast, .northWest, .southEast, .southWest]

structure Board where
  width : Nat
  height : Nat
  floor : List Cell
  rollingTraps : List Cell := []
  /-- All intact doors, including ones omitted from traversable floor. -/
  doors : List Cell := []
  /-- Metadata only: the completion goal does not require a staircase. -/
  exit : Cell := 0
  deriving Repr, BEq, DecidableEq, Inhabited

structure State where
  player : Cell
  boulders : List Cell
  /-- Original PIT and HOLE traps, represented together because both consume
  one boulder and disappear in this monster-free profile. -/
  holes : List Cell
  deriving Repr, BEq, DecidableEq, Inhabited

def Goal (state : State) : Prop := state.holes = []
instance (state : State) : Decidable (Goal state) := inferInstanceAs (Decidable (state.holes = []))
def goal (state : State) : Bool := state.holes.isEmpty

theorem goal_iff (state : State) : goal state = true ↔ Goal state := by
  simp [goal, Goal]

/-- Flattened cells retain two-dimensional boundaries; east/west never wrap. -/
def advance (board : Board) (cell : Cell) (direction : Dir) : Option Cell :=
  if board.width = 0 ∨ cell ≥ board.width * board.height then none
  else
    let x := Int.ofNat (cell % board.width) + direction.dx
    let y := Int.ofNat (cell / board.width) + direction.dy
    if 0 ≤ x ∧ x < Int.ofNat board.width ∧ 0 ≤ y ∧ y < Int.ofNat board.height then
      some (x.toNat + board.width * y.toNat)
    else none

def blocked (board : Board) (state : State) (cell : Cell) : Bool :=
  (!board.floor.contains cell && !board.doors.contains cell) || state.boulders.contains cell

private def sideBlocked (board : Board) (state : State) (direction : Dir) : Bool :=
  match advance board state.player direction with
  | none => true
  | some cell => blocked board state cell

/-- NetHack's Sokoban `bad_rock` test counts walls and boulders on BOTH
orthogonal side cells. Pits do not themselves count as corner walls. -/
def cornerBlocked (board : Board) (state : State) (direction : Dir) : Bool :=
  direction.diagonal &&
    sideBlocked board state direction.sides.1 && sideBlocked board state direction.sides.2

structure PushResult where
  boulders : List Cell
  filled : Option Cell
  landing : Cell
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Static relaxation of a rolling ray, ignoring other boulders and open
hazards. Including the starting cell adds only a harmless positive-cost loop
to lower-bound certificates. Every actual landing is a member. -/
def rayTargets (board : Board) (direction : Dir) : Nat → Cell → List Cell
  | 0, current => [current]
  | fuel + 1, current =>
    current :: match advance board current direction with
      | none => []
      | some next =>
        if board.doors.contains next || !board.floor.contains next then []
        else rayTargets board direction fuel next

/-- Static relaxed push edges retain the necessary floor support behind the
boulder. They deliberately ignore movable obstacles and premature hole stops. -/
def pushTargets (board : Board) (source : Cell) (direction : Dir) : List Cell := Id.run do
  if direction.diagonal then return []
  let some behind := advance board source direction.opposite | return []
  if !board.floor.contains behind || board.doors.contains behind then return []
  let some destination := advance board source direction | return []
  if !board.floor.contains destination || board.doors.contains destination then return []
  if board.rollingTraps.contains destination then
    return rayTargets board direction (board.width * board.height + 1) source
  return [destination]

/-- The travelling boulder has already been removed. Source Sokoban launch
endpoints coincide with the trap itself (no generated ammunition), so a
triggered cardinal roll continues to a wall/edge or the first open pit/hole.
Fuel is a totality guard; a straight line has fewer than area+1 cells. -/
def roll (board : Board) (stationary holes : List Cell) (direction : Dir) :
    Nat → Cell → Option PushResult
  | 0, _ => none
  | fuel + 1, current =>
    match advance board current direction with
    | none => some ⟨current :: stationary, none, current⟩
    | some next =>
      if board.doors.contains next then none
      else if !board.floor.contains next then some ⟨current :: stationary, none, current⟩
      else if stationary.contains next then none
      else if holes.contains next then some ⟨stationary, some next, next⟩
      else roll board stationary holes direction fuel next

def pushBoulder (board : Board) (state : State) (source : Cell)
    (direction : Dir) : Option PushResult := do
  if direction.diagonal then none else pure ()
  let behind ← advance board source direction.opposite
  if !board.floor.contains behind || board.doors.contains behind then none else pure ()
  let destination ← advance board source direction
  if !board.floor.contains destination || board.doors.contains destination ||
      state.boulders.contains destination then none else pure ()
  let remaining := state.boulders.erase source
  if state.holes.contains destination then
    return ⟨remaining, some destination, destination⟩
  else if board.rollingTraps.contains destination then
    roll board remaining state.holes direction (board.width * board.height + 1) source
  else
    return ⟨destination :: remaining, none, destination⟩

def afterFill (holes : List Cell) (filled : Option Cell) : List Cell :=
  match filled with
  | none => holes
  | some cell => holes.erase cell

structure Transition where
  state : State
  pushed : Bool
  filled : Option Cell
  pushSource : Option Cell := none
  landing : Option Cell := none
  deriving Repr, BEq, DecidableEq, Inhabited

def Transition.pushCost (transition : Transition) : Nat := if transition.pushed then 1 else 0
def Transition.consumed (transition : Transition) : Bool := transition.filled.isSome

/-- Only admitted successful player displacements are transitions. Ordinary
walks cost zero pushes; every displacement costs one move. -/
private def stepCore (board : Board) (state : State) (direction : Dir) : Option Transition := do
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

/-- The pure profile excludes standing in a wall, doorway, boulder or open
hazard. These are checked physical premises, not assumptions about a searcher. -/
def standingAllowed (board : Board) (state : State) : Bool :=
  board.floor.contains state.player && !board.doors.contains state.player &&
    !state.boulders.contains state.player && !state.holes.contains state.player

def step (board : Board) (state : State) (direction : Dir) : Option Transition := do
  if !standingAllowed board state then none else pure ()
  stepCore board state direction

theorem step_core_of (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    stepCore board state direction = some transition := by
  cases standing : standingAllowed board state with
  | false => simp [step, standing] at checked
  | true => simpa [step, standing] using checked

theorem step_player_clear (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    state.player ∈ board.floor ∧ state.player ∉ board.doors ∧
      state.player ∉ state.boulders ∧ state.player ∉ state.holes := by
  cases standing : standingAllowed board state with
  | false => simp [step, standing] at checked
  | true => simpa [standingAllowed, and_assoc] using standing

/-- Input invariants needed when relating this model to the original world.
The executable transition is total even on other inputs. -/
def WellFormed (board : Board) (state : State) : Prop :=
  board.width > 0 ∧ board.height > 0 ∧
  board.floor.Nodup ∧ state.boulders.Nodup ∧ state.holes.Nodup ∧
  state.player ∈ board.floor ∧ state.player ∉ state.boulders ∧ state.player ∉ state.holes ∧
  (∀ cell ∈ state.boulders, cell ∈ board.floor ∧ cell ∉ state.holes) ∧
  (∀ cell ∈ state.holes, cell ∈ board.floor) ∧
  (∀ cell ∈ board.floor, cell < board.width * board.height)

instance (board : Board) (state : State) : Decidable (WellFormed board state) := by
  unfold WellFormed
  infer_instance

structure RunResult where
  state : State
  pushes : Nat
  moves : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def run (board : Board) (state : State) : List Dir → Option RunResult
  | [] => some ⟨state, 0, 0⟩
  | direction :: rest => do
    let next ← step board state direction
    let result ← run board next.state rest
    return ⟨result.state, next.pushCost + result.pushes, 1 + result.moves⟩

/-- Logical finite trace semantics, independent of the recursive path checker. -/
inductive Trace (board : Board) : State → List Dir → State → Nat → Nat → Prop where
  | nil (state) : Trace board state [] state 0 0
  | cons {state direction next rest final pushes moves}
      (head : step board state direction = some next)
      (tail : Trace board next.state rest final pushes moves) :
      Trace board state (direction :: rest) final (next.pushCost + pushes) (1 + moves)

theorem run_sound (board : Board) (state : State) (directions : List Dir)
    (result : RunResult) (checked : run board state directions = some result) :
    Trace board state directions result.state result.pushes result.moves := by
  induction directions generalizing state result with
  | nil =>
    simp [run] at checked
    subst result
    exact Trace.nil state
  | cons direction rest ih =>
    cases head : step board state direction with
    | none => simp [run, head] at checked
    | some next =>
      cases tail : run board next.state rest with
      | none => simp [run, head, tail] at checked
      | some final =>
        simp [run, head, tail] at checked
        subst result
        exact Trace.cons head (ih next.state final tail)

theorem Trace.moves_eq_length {board : Board} {state : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board state directions final pushes moves) :
    moves = directions.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp [ih, Nat.add_comm]

theorem run_moves_eq_length (board : Board) (state : State) (directions : List Dir)
    (result : RunResult) (checked : run board state directions = some result) :
    result.moves = directions.length :=
  (run_sound board state directions result checked).moves_eq_length

/-- Long proposed solutions may be kernel-checked in independent finite
chunks and combined without trusting an external path concatenator. -/
theorem run_append_of (board : Board) (state : State) (first second : List Dir)
    (firstResult secondResult : RunResult)
    (checkedFirst : run board state first = some firstResult)
    (checkedSecond : run board firstResult.state second = some secondResult) :
    run board state (first ++ second) = some
      {state := secondResult.state, pushes := firstResult.pushes + secondResult.pushes,
        moves := firstResult.moves + secondResult.moves} := by
  induction first generalizing state firstResult with
  | nil =>
    simp [run] at checkedFirst
    subst firstResult
    simpa using checkedSecond
  | cons direction rest ih =>
    cases head : step board state direction with
    | none => simp [run, head] at checkedFirst
    | some next =>
      cases tail : run board next.state rest with
      | none => simp [run, head, tail] at checkedFirst
      | some middle =>
        simp [run, head, tail] at checkedFirst
        subst firstResult
        have combined := ih next.state middle tail checkedSecond
        simpa [run, head, combined, Nat.add_assoc] using combined

/-- `afterFill` can remove at most one original hazard, including a long roll. -/
theorem afterFill_length (holes : List Cell) (filled : Option Cell) :
    holes.length ≤ (afterFill holes filled).length + 1 := by
  cases filled with
  | none => simp [afterFill]
  | some cell =>
    simp only [afterFill]
    have h := List.le_length_erase (l := holes) (a := cell)
    omega

/-- Every checked transition is either a walk preserving all puzzle objects,
or exactly one call to the concrete push algorithm on a present boulder. -/
theorem step_cases (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    (transition.pushed = false ∧ transition.state.boulders = state.boulders ∧
      transition.state.holes = state.holes) ∨
    (∃ source result, source ∈ state.boulders ∧
      pushBoulder board state source direction = some result ∧
      transition.pushed = true ∧ transition.state.boulders = result.boulders ∧
      transition.state.holes = afterFill state.holes result.filled) := by
  have checked := step_core_of board state direction transition checked
  cases completed : goal state with
  | true => simp [stepCore, completed] at checked
  | false =>
    cases adjacent : advance board state.player direction with
    | none => simp [stepCore, completed, adjacent] at checked
    | some source =>
      by_cases present : source ∈ state.boulders
      · cases pushed : pushBoulder board state source direction with
        | none => simp [stepCore, completed, adjacent, present, pushed] at checked
        | some result =>
          simp [stepCore, completed, adjacent, present, pushed] at checked
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inr ⟨source, result, present, pushed, rfl, rfl, rfl⟩
      · by_cases hazard : source ∈ state.holes
        · simp [stepCore, completed, adjacent, present, hazard] at checked
        · simp [stepCore, completed, adjacent, present, hazard] at checked
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inl ⟨rfl, rfl, rfl⟩

theorem step_cases_floor (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    (transition.pushed = false ∧ transition.state.boulders = state.boulders ∧
      transition.state.holes = state.holes) ∨
    (∃ source result, source ∈ board.floor ∧ source ∈ state.boulders ∧
      pushBoulder board state source direction = some result ∧
      transition.pushed = true ∧ transition.state.boulders = result.boulders ∧
      transition.state.holes = afterFill state.holes result.filled) := by
  have checked := step_core_of board state direction transition checked
  cases completed : goal state with
  | true => simp [stepCore, completed] at checked
  | false =>
    cases adjacent : advance board state.player direction with
    | none => simp [stepCore, completed, adjacent] at checked
    | some source =>
      by_cases present : source ∈ state.boulders
      · cases pushed : pushBoulder board state source direction with
        | none => simp [stepCore, completed, adjacent, present, pushed] at checked
        | some result =>
          simp [stepCore, completed, adjacent, present, pushed] at checked
          have floor := checked.1.1.1
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inr ⟨source, result, floor, present, pushed, rfl, rfl, rfl⟩
      · by_cases hazard : source ∈ state.holes
        · simp [stepCore, completed, adjacent, present, hazard] at checked
        · simp [stepCore, completed, adjacent, present, hazard] at checked
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inl ⟨rfl, rfl, rfl⟩

/-- Full step metadata for independent finite pattern checkers: the supporting
player cell is the actual original cell, not an invented push-graph node. -/
theorem step_cases_full (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    (∃ target, advance board state.player direction = some target ∧ target ∈ board.floor ∧
      target ∉ state.boulders ∧ target ∉ state.holes ∧
      transition = {state := {state with player := target}, pushed := false, filled := none}) ∨
    (∃ source result, advance board state.player direction = some source ∧ source ∈ board.floor ∧
      source ∈ state.boulders ∧ pushBoulder board state source direction = some result ∧
      transition = {state := {player := source, boulders := result.boulders, holes := afterFill state.holes result.filled}, pushed := true, filled := result.filled, pushSource := some source, landing := some result.landing}) := by
  have checked := step_core_of board state direction transition checked
  cases completed : goal state with
  | true => simp [stepCore, completed] at checked
  | false =>
    cases adjacent : advance board state.player direction with
    | none => simp [stepCore, completed, adjacent] at checked
    | some source =>
      by_cases present : source ∈ state.boulders
      · cases pushed : pushBoulder board state source direction with
        | none => simp [stepCore, completed, adjacent, present, pushed] at checked
        | some result =>
          simp [stepCore, completed, adjacent, present, pushed] at checked
          have floor := checked.1.1.1
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inr ⟨source, result, rfl, floor, present, pushed, rfl⟩
      · by_cases hazard : source ∈ state.holes
        · simp [stepCore, completed, adjacent, present, hazard] at checked
        · simp [stepCore, completed, adjacent, present, hazard] at checked
          have floor := checked.1.1.1
          rcases checked with ⟨_, checked⟩
          subst transition
          exact Or.inl ⟨source, rfl, floor, present, hazard, rfl⟩

theorem step_player_floor (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    transition.state.player ∈ board.floor := by
  rcases step_cases_full board state direction transition checked with walk | pushed
  · rcases walk with ⟨target, _, floor, _, _, shape⟩
    simpa only [shape] using floor
  · rcases pushed with ⟨source, result, _, floor, _, _, shape⟩
    simpa only [shape] using floor


theorem step_holes_length (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    state.holes.length ≤ transition.pushCost + transition.state.holes.length := by
  rcases step_cases board state direction transition checked with walk | push
  · rcases walk with ⟨cost, _, holes⟩
    simp [Transition.pushCost, cost, holes]
  · rcases push with ⟨source, result, _, _, cost, _, holes⟩
    have bound := afterFill_length state.holes result.filled
    simp [Transition.pushCost, cost, holes]
    omega

/-- A collision-free roll either leaves its one travelling boulder at its
landing cell or consumes it in exactly one present original hazard. -/
theorem mem_rayTargets_self (board : Board) (direction : Dir) (fuel current : Nat) :
    current ∈ rayTargets board direction fuel current := by
  cases fuel <;> simp [rayTargets]

theorem roll_spec (board : Board) (stationary holes : List Cell) (direction : Dir)
    (fuel current : Nat) (result : PushResult)
    (checked : roll board stationary holes direction fuel current = some result) :
    ((result.filled = none ∧ result.boulders = result.landing :: stationary) ∨
      (result.filled = some result.landing ∧ result.landing ∈ holes ∧
        result.boulders = stationary)) ∧
    result.landing ∈ rayTargets board direction fuel current := by
  induction fuel generalizing current result with
  | zero => simp [roll] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none =>
      simp [roll, adjacent] at checked
      subst result
      exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [rayTargets, adjacent]⟩
    | some next =>
      by_cases door : next ∈ board.doors
      · simp [roll, adjacent, door] at checked
      · by_cases floor : next ∈ board.floor
        · by_cases collision : next ∈ stationary
          · simp [roll, adjacent, door, floor, collision] at checked
          · by_cases hazard : next ∈ holes
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              subst result
              exact ⟨Or.inr ⟨rfl, hazard, rfl⟩, by
                simp [rayTargets, adjacent, door, floor, mem_rayTargets_self]⟩
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              have smaller := ih next result checked
              exact ⟨smaller.1, by simp [rayTargets, adjacent, door, floor, smaller.2]⟩
        · simp [roll, adjacent, door, floor] at checked
          subst result
          exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [rayTargets, adjacent]⟩

/-- The complete concrete push algorithm refines the static relaxed edge set
and changes precisely one boulder, plus at most one present original hazard. -/
theorem pushBoulder_spec (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult)
    (checked : pushBoulder board state source direction = some result) :
    ((result.filled = none ∧
        result.boulders = result.landing :: state.boulders.erase source) ∨
      (result.filled = some result.landing ∧ result.landing ∈ state.holes ∧
        result.boulders = state.boulders.erase source)) ∧
    result.landing ∈ pushTargets board source direction := by
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      by_cases behindFloor : behind ∈ board.floor
      · by_cases behindDoor : behind ∈ board.doors
        · simp [pushBoulder, diagonal, support, behindFloor, behindDoor] at checked
        · cases adjacent : advance board source direction with
          | none => simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent] at checked
          | some destination =>
            by_cases floor : destination ∈ board.floor
            · by_cases door : destination ∈ board.doors
              · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door] at checked
              · by_cases collision : destination ∈ state.boulders
                · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision] at checked
                · by_cases hazard : destination ∈ state.holes
                  · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard] at checked
                    subst result
                    refine ⟨Or.inr ⟨rfl, hazard, rfl⟩, ?_⟩
                    by_cases rolling : destination ∈ board.rollingTraps
                    · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling,
                        rayTargets, mem_rayTargets_self]
                    · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling]
                  · by_cases rolling : destination ∈ board.rollingTraps
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      have rolled := roll_spec board (state.boulders.erase source) state.holes direction
                        (board.width * board.height + 1) source result checked
                      exact ⟨rolled.1, by
                        simpa [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling] using rolled.2⟩
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      subst result
                      exact ⟨Or.inl ⟨rfl, rfl⟩, by
                        simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling]⟩
            · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor] at checked
      · simp [pushBoulder, diagonal, support, behindFloor] at checked

/-- Filling a hazard consumes exactly one already present boulder. Ordinary
walking, pushing and non-consuming rolls preserve both counts. -/
theorem step_conservation (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    state.boulders.length + transition.state.holes.length =
      transition.state.boulders.length + state.holes.length := by
  rcases step_cases_floor board state direction transition checked with walk | pushed
  · rcases walk with ⟨_, boxes, holes⟩
    simp [boxes, holes]
  · rcases pushed with ⟨source, result, _, member, pushChecked, _, boxes, holes⟩
    have erasedBox := List.length_erase_of_mem member
    have boxPositive := List.length_pos_of_mem member
    rcases (pushBoulder_spec board state source direction result pushChecked).1 with stays | consumes
    · rcases stays with ⟨filled, shape⟩
      simp only [boxes, holes, filled, shape, afterFill, List.length_cons]
      omega
    · rcases consumes with ⟨filled, hazard, shape⟩
      have erasedHole := List.length_erase_of_mem hazard
      have holePositive := List.length_pos_of_mem hazard
      simp only [boxes, holes, filled, shape, afterFill]
      omega

/-- The complete trace preserves the initial boulder/hazard surplus. -/
theorem Trace.conservation {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    initial.boulders.length + final.holes.length =
      final.boulders.length + initial.holes.length := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
    have single := step_conservation _ _ _ _ head
    omega

theorem afterFill_sublist (holes : List Cell) (filled : Option Cell) :
    List.Sublist (afterFill holes filled) holes := by
  cases filled with
  | none => exact List.Sublist.refl holes
  | some cell => exact List.erase_sublist

theorem step_holes_sublist (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (checked : step board state direction = some transition) :
    List.Sublist transition.state.holes state.holes := by
  rcases step_cases board state direction transition checked with walk | pushed
  · rcases walk with ⟨_, _, holes⟩
    rw [holes]
    exact List.Sublist.refl _
  · rcases pushed with ⟨source, result, _, _, _, _, holes⟩
    rw [holes]
    exact afterFill_sublist state.holes result.filled

/-- No admitted action creates or reorders an original remaining hazard. -/
theorem Trace.holes_sublist {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) :
    List.Sublist final.holes initial.holes := by
  induction trace with
  | nil => exact List.Sublist.refl _
  | cons head tail ih => exact ih.trans (step_holes_sublist _ _ _ _ head)

theorem roll_nodup (board : Board) (stationary holes : List Cell) (direction : Dir)
    (fuel current : Nat) (result : PushResult) (unique : stationary.Nodup)
    (fresh : current ∉ stationary)
    (checked : roll board stationary holes direction fuel current = some result) :
    result.boulders.Nodup := by
  induction fuel generalizing current result with
  | zero => simp [roll] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none =>
      simp [roll, adjacent] at checked
      subst result
      exact List.nodup_cons.mpr ⟨fresh, unique⟩
    | some next =>
      by_cases door : next ∈ board.doors
      · simp [roll, adjacent, door] at checked
      · by_cases floor : next ∈ board.floor
        · by_cases collision : next ∈ stationary
          · simp [roll, adjacent, door, floor, collision] at checked
          · by_cases hazard : next ∈ holes
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              subst result
              exact unique
            · simp [roll, adjacent, door, floor, collision, hazard] at checked
              exact ih next result collision checked
        · simp [roll, adjacent, door, floor] at checked
          subst result
          exact List.nodup_cons.mpr ⟨fresh, unique⟩


/-- The restricted rolling profile never creates a boulder stack. -/
theorem pushBoulder_nodup (board : Board) (state : State) (source : Cell)
    (direction : Dir) (result : PushResult) (unique : state.boulders.Nodup)
    (checked : pushBoulder board state source direction = some result) :
    result.boulders.Nodup := by
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, diagonal] at checked
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushBoulder, diagonal, support] at checked
    | some behind =>
      by_cases behindFloor : behind ∈ board.floor
      · by_cases behindDoor : behind ∈ board.doors
        · simp [pushBoulder, diagonal, support, behindFloor, behindDoor] at checked
        · cases adjacent : advance board source direction with
          | none => simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent] at checked
          | some destination =>
            by_cases floor : destination ∈ board.floor
            · by_cases door : destination ∈ board.doors
              · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door] at checked
              · by_cases collision : destination ∈ state.boulders
                · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision] at checked
                · by_cases hazard : destination ∈ state.holes
                  · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard] at checked
                    subst result
                    exact List.Nodup.erase source unique
                  · by_cases rolling : destination ∈ board.rollingTraps
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      exact roll_nodup board (state.boulders.erase source) state.holes direction
                        (board.width * board.height + 1) source result
                        (List.Nodup.erase source unique) (List.Nodup.not_mem_erase unique) checked
                    · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, collision, hazard, rolling] at checked
                      subst result
                      exact List.nodup_cons.mpr ⟨fun member => collision (List.mem_of_mem_erase member),
                        List.Nodup.erase source unique⟩
            · simp [pushBoulder, diagonal, support, behindFloor, behindDoor, adjacent, floor] at checked
      · simp [pushBoulder, diagonal, support, behindFloor] at checked

theorem step_boulders_nodup (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (unique : state.boulders.Nodup)
    (checked : step board state direction = some transition) :
    transition.state.boulders.Nodup := by
  rcases step_cases board state direction transition checked with walk | pushed
  · rcases walk with ⟨_, boxes, _⟩
    simpa only [boxes] using unique
  · rcases pushed with ⟨source, result, _, pushChecked, _, boxes, _⟩
    simpa only [boxes] using pushBoulder_nodup board state source direction result unique pushChecked

theorem Trace.boulders_nodup {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (unique : initial.boulders.Nodup) : final.boulders.Nodup := by
  revert unique
  induction trace with
  | nil => exact fun unique => unique
  | cons head tail ih =>
    intro unique
    exact ih (step_boulders_nodup _ _ _ _ unique head)

theorem Trace.holes_nodup {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (unique : initial.holes.Nodup) : final.holes.Nodup :=
  trace.holes_sublist.nodup unique

theorem rayTargets_floor (board : Board) (direction : Dir) (fuel current cell : Nat)
    (standing : current ∈ board.floor)
    (member : cell ∈ rayTargets board direction fuel current) : cell ∈ board.floor := by
  induction fuel generalizing current with
  | zero =>
    simp [rayTargets] at member
    simpa [member] using standing
  | succ fuel ih =>
    simp only [rayTargets, List.mem_cons] at member
    rcases member with same | later
    · simpa [same] using standing
    · cases adjacent : advance board current direction with
      | none => simp [adjacent] at later
      | some next =>
        by_cases door : next ∈ board.doors
        · simp [adjacent, door] at later
        · by_cases floor : next ∈ board.floor
          · simp [adjacent, door, floor] at later
            exact ih next floor later
          · simp [adjacent, door, floor] at later

theorem pushTargets_floor (board : Board) (source : Cell) (direction : Dir)
    (standing : source ∈ board.floor) (cell : Cell)
    (member : cell ∈ pushTargets board source direction) : cell ∈ board.floor := by
  cases diagonal : direction.diagonal with
  | true => simp [pushTargets, diagonal] at member
  | false =>
    cases support : advance board source direction.opposite with
    | none => simp [pushTargets, diagonal, support] at member
    | some behind =>
      by_cases behindFloor : behind ∈ board.floor
      · by_cases behindDoor : behind ∈ board.doors
        · simp [pushTargets, diagonal, support, behindFloor, behindDoor] at member
        · cases adjacent : advance board source direction with
          | none => simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent] at member
          | some destination =>
            by_cases floor : destination ∈ board.floor
            · by_cases door : destination ∈ board.doors
              · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door] at member
              · by_cases rolling : destination ∈ board.rollingTraps
                · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling] at member
                  exact rayTargets_floor board direction _ source cell standing member
                · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor, door, rolling] at member
                  simpa [member] using floor
            · simp [pushTargets, diagonal, support, behindFloor, behindDoor, adjacent, floor] at member
      · simp [pushTargets, diagonal, support, behindFloor] at member

theorem step_boulders_floor (board : Board) (state : State) (direction : Dir)
    (transition : Transition) (standing : ∀ cell ∈ state.boulders, cell ∈ board.floor)
    (checked : step board state direction = some transition) :
    ∀ cell ∈ transition.state.boulders, cell ∈ board.floor := by
  rcases step_cases_floor board state direction transition checked with walk | pushed
  · rcases walk with ⟨_, boxes, _⟩
    simpa only [boxes] using standing
  · rcases pushed with ⟨source, result, sourceFloor, _, pushChecked, _, boxes, _⟩
    have spec := pushBoulder_spec board state source direction result pushChecked
    have landingFloor := pushTargets_floor board source direction sourceFloor result.landing spec.2
    rcases spec.1 with stays | consumes
    · rcases stays with ⟨_, shape⟩
      intro cell member
      rw [boxes, shape] at member
      rcases List.mem_cons.mp member with same | later
      · simpa [same] using landingFloor
      · exact standing cell (List.mem_of_mem_erase later)
    · rcases consumes with ⟨_, _, shape⟩
      intro cell member
      rw [boxes, shape] at member
      exact standing cell (List.mem_of_mem_erase member)

theorem Trace.boulders_floor {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (standing : ∀ cell ∈ initial.boulders, cell ∈ board.floor) :
    ∀ cell ∈ final.boulders, cell ∈ board.floor := by
  revert standing
  induction trace with
  | nil => exact fun standing => standing
  | cons head tail ih =>
    intro standing
    exact ih (step_boulders_floor _ _ _ _ standing head)

theorem Trace.player_floor {board : Board} {initial : State} {directions : List Dir}
    {final : State} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (standing : initial.player ∈ board.floor) : final.player ∈ board.floor := by
  revert standing
  induction trace with
  | nil => exact fun standing => standing
  | cons head tail ih =>
    intro _
    exact ih (step_player_floor _ _ _ _ head)

end NetHack.Sokoban
