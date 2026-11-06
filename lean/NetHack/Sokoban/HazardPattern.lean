/- A Boolean occupancy oracle for the unchanged Model, including hazards.
The oracle records only the landing/fill effect; it does not replace the
physical board, alter rolling rules, or assign costs to a push graph. -/
import NetHack.Sokoban.PatternCorrection
import NetHack.Sokoban.ClosedSupport
import NetHack.Sokoban.FiniteTopology

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.HazardPattern
open PatternCorrection LowerBounds

inductive Ending where
  | stay (landing : Cell)
  | fill (hole : Cell)
  deriving DecidableEq, BEq, Repr

def ending (result : PushResult) : Ending :=
  match result.filled with
  | none => .stay result.landing
  | some hole => .fill hole

def rollOracle (board : Board) (boxes holes : Pattern) (direction : Dir) :
    Nat → Cell → Option Ending
  | 0, _ => none
  | fuel + 1, current =>
    match advance board current direction with
    | none => some (.stay current)
    | some next =>
      if board.doors.contains next then none
      else if !board.floor.contains next then some (.stay current)
      else if boxes next then none
      else if holes next then some (.fill next)
      else rollOracle board boxes holes direction fuel next

/-- The endpoint oracle has exactly the original successful rolling result.
In particular a collision is failure, and the first open hazard consumes the
boulder before any later hazard can be considered. No randomness is assumed. -/
theorem rollOracle_exact (board : Board) (boxes holes : List Cell) (direction : Dir)
    (fuel current : Nat) :
    (roll board boxes holes direction fuel current).map ending =
      rollOracle board (project boxes) (project holes) direction fuel current := by
  induction fuel generalizing current with
  | zero => rfl
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none => simp [roll, rollOracle, adjacent, ending]
    | some next =>
      cases door : board.doors.contains next <;>
        cases floor : board.floor.contains next <;>
        cases box : boxes.contains next <;>
        cases hole : holes.contains next <;>
        simp only [roll, rollOracle, project, adjacent, door, floor, box, hole, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none, ending, ih]

def pushOracle (board : Board) (boxes holes : Pattern) (source : Cell)
    (direction : Dir) : Option Ending := do
  if direction.diagonal then none else pure ()
  let behind ← advance board source direction.opposite
  if !board.floor.contains behind || board.doors.contains behind then none else pure ()
  let destination ← advance board source direction
  if !board.floor.contains destination || board.doors.contains destination || boxes destination then
    none else pure ()
  if holes destination then return .fill destination
  else if board.rollingTraps.contains destination then
    rollOracle board (change boxes source none) holes direction (board.width * board.height + 1) source
  else return .stay destination

theorem pushOracle_exact (board : Board) (state : State) (unique : state.boulders.Nodup)
    (source : Cell) (direction : Dir) :
    (pushBoulder board state source direction).map ending =
      pushOracle board (project state.boulders) (project state.holes) source direction := by
  have erased := project_erase state.boulders unique source
  change (pushBoulder board state source direction).map ending =
    pushOracle board state.boulders.contains state.holes.contains source direction
  cases diagonal : direction.diagonal with
  | true => simp [pushBoulder, pushOracle, diagonal]
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp [pushBoulder, pushOracle, diagonal, behind]
    | some cell =>
      simp only [pushBoulder, pushOracle, diagonal, Bool.false_eq_true, ↓reduceIte,
        bind, pure, Option.bind_some, behind]
      split
      · simp
      · cases destination : advance board source direction with
        | none => simp [destination]
        | some first =>
          simp only [destination, Option.bind_some]
          split
          · simp
          · split
            · rfl
            · split
              · exact (rollOracle_exact board (state.boulders.erase source) state.holes direction _ _).trans
                  (by rw [erased]; rfl)
              · rfl

/-- Hazard bits use separate variable names. These are decision-diagram
indices, never extra physical cells or a different Sokoban map. -/
def combined (separator : Nat) (state : State) : Pattern :=
  fun cell => if cell < separator then state.boulders.contains cell
    else state.holes.contains (cell - separator)

def boxes (cells : List Cell) (pattern : Pattern) : Pattern :=
  fun cell => cells.contains cell && pattern cell

def hazards (separator : Nat) (original : List Cell) (pattern : Pattern) : Pattern :=
  fun cell => original.contains cell && pattern (separator + cell)

theorem hazards_combined (separator : Nat) (original : List Cell) (state : State)
    (subset : state.holes ⊆ original) :
    hazards separator original (combined separator state) = project state.holes := by
  funext cell
  have separated : ¬separator + cell < separator := by omega
  have cancel : separator + cell - separator = cell := by omega
  simp only [hazards, combined, separated, ↓reduceIte, cancel, project]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true_iff, List.contains_iff_mem]
  exact ⟨fun h => h.2, fun h => ⟨subset h, h⟩⟩

theorem boxes_combined (separator : Nat) (cells : List Cell) (state : State)
    (bounds : ∀ cell ∈ cells, cell < separator) (subset : state.boulders ⊆ cells) :
    boxes cells (combined separator state) = project state.boulders := by
  funext cell
  by_cases member : cell ∈ cells
  · simp [boxes, combined, project, member, bounds cell member]
  · have absent : cell ∉ state.boulders := fun h => member (subset h)
    simp [boxes, project, member, absent]

inductive Outcome where
  | walk (target : Cell)
  | push (source : Cell) (result : Ending)
  deriving DecidableEq, BEq, Repr

private def side (board : Board) (boxes : Pattern) (hero : Cell) (direction : Dir) : Bool :=
  match advance board hero direction with
  | none => true
  | some cell => (!board.floor.contains cell && !board.doors.contains cell) || boxes cell

def corner (board : Board) (boxes : Pattern) (hero : Cell) (direction : Dir) : Bool :=
  direction.diagonal && side board boxes hero direction.sides.1 &&
    side board boxes hero direction.sides.2

theorem corner_project (board : Board) (state : State) (direction : Dir) :
    corner board (project state.boulders) state.player direction =
      cornerBlocked board state direction := rfl

def stepOracle (board : Board) (boxes holes : Pattern) (hero : Cell)
    (direction : Dir) : Option Outcome := do
  if boxes hero || holes hero then none else pure ()
  let target ← advance board hero direction
  if !board.floor.contains target || board.doors.contains target || corner board boxes hero direction then
    none else pure ()
  if boxes target then
    let result ← pushOracle board boxes holes target direction
    return .push target result
  else if holes target then none else return .walk target

/-- A relation to the actual ordered lists, retaining the original push cost
and exact consumption. Both lists, rather than a proposer region, determine
the result of every admitted action. -/
def Matches (state : State) (t : Transition) : Outcome → Prop
  | .walk target =>
    t = {state := {state with player := target}, pushed := false, filled := none}
  | .push source (.stay landing) => source ∈ state.boulders ∧
    t = {state := {player := source, boulders := landing :: state.boulders.erase source, holes := state.holes}, pushed := true, filled := none, pushSource := some source, landing := some landing}
  | .push source (.fill hole) => source ∈ state.boulders ∧ hole ∈ state.holes ∧
    t = {state := {player := source, boulders := state.boulders.erase source, holes := state.holes.erase hole}, pushed := true, filled := some hole, pushSource := some source, landing := some hole}

/-- Every successful original Model step is represented. The oracle does not
need to reject post-goal actions: Model already rejects them, and admitting
extra oracle actions can only strengthen later certificate obligations. -/
theorem stepOracle_covers (board : Board) (state : State) (unique : state.boulders.Nodup)
    (direction : Dir) (t : Transition) (checked : step board state direction = some t) :
    ∃ outcome, stepOracle board (project state.boulders) (project state.holes)
      state.player direction = some outcome ∧ Matches state t outcome := by
  have standing := step_player_clear board state direction t checked
  have heroBox : project state.boulders state.player = false := by simp [project, standing.2.2.1]
  have heroHole : project state.holes state.player = false := by simp [project, standing.2.2.2]
  have clear : corner board (project state.boulders) state.player direction = false :=
    (corner_project board state direction).trans
      (FiniteTopology.step_corner_clear board state direction t checked)
  rcases step_cases_full board state direction t checked with walked | pushed
  · rcases walked with ⟨target, adjacent, floor, boxClear, holeClear, shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t target adjacent checked
    refine ⟨.walk target, ?_, shape⟩
    have ft : board.floor.contains target = true := by simp [floor]
    have dc : board.doors.contains target = false := by simp [door]
    have bc : project state.boulders target = false := by simp [project, boxClear]
    have hc : project state.holes target = false := by simp [project, holeClear]
    simp only [stepOracle, heroBox, heroHole, adjacent, ft, dc, bc, hc, clear,
      Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some]
  · rcases pushed with ⟨source, result, adjacent, floor, present, pushed, shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t source adjacent checked
    have oracle := pushOracle_exact board state unique source direction
    rw [pushed] at oracle
    have produces : stepOracle board (project state.boulders) (project state.holes)
        state.player direction = some (.push source (ending result)) := by
      have doorClear : board.doors.contains source = false := by simp [door]
      have floorTrue : board.floor.contains source = true := by simp [floor]
      have boxTrue : project state.boulders source = true := by simp [project, present]
      simp only [stepOracle, heroBox, heroHole, Bool.false_or, Bool.false_eq_true,
        ↓reduceIte, bind, pure, Option.bind_some, adjacent, floorTrue, Bool.not_true,
        doorClear, Bool.or_false, clear, boxTrue, Bool.or_self, Bool.true_eq_false]
      rw [← oracle]
      rfl
    rcases (pushBoulder_spec board state source direction result pushed).1 with stay | fill
    · rcases stay with ⟨unfilled, shapeBoxes⟩
      refine ⟨.push source (.stay result.landing), ?_, present, ?_⟩
      · simpa only [ending, unfilled] using produces
      · subst t
        simp only [unfilled, shapeBoxes, afterFill]
    · rcases fill with ⟨filled, hazard, shapeBoxes⟩
      refine ⟨.push source (.fill result.landing), ?_, present, hazard, ?_⟩
      · simpa only [ending, filled] using produces
      · subst t
        simp only [filled, shapeBoxes, afterFill]

/-- Occupancy updates preserve the distinction between physical boulders and
hazard variables. The two erasures on a fill are both represented. -/
def afterPattern (separator : Nat) (pattern : Pattern) : Outcome → Pattern
  | .walk _ => pattern
  | .push source (.stay landing) => change pattern source (some landing)
  | .push source (.fill hole) => change (change pattern source none) (separator + hole) none

def nextHero : Outcome → Cell
  | .walk target => target
  | .push source _ => source

def slack (potential : Potential) : Outcome → Int
  | .walk _ => 0
  | .push source (.stay landing) => 1 + potential.boulder landing - potential.boulder source
  | .push source (.fill hole) => 1 - potential.boulder source - potential.hole hole

theorem combined_stay (separator : Nat) (state : State) (unique : state.boulders.Nodup)
    (source landing : Cell) (sourceBound : source < separator) (landingBound : landing < separator) :
    combined separator {player := source, boulders := landing :: state.boulders.erase source, holes := state.holes} = change (combined separator state) source (some landing) := by
  funext cell
  by_cases small : cell < separator
  · simpa only [combined, small, ↓reduceIte, project, change] using
      congrFun (project_replace state.boulders unique source landing) cell
  · have ns : source ≠ cell := fun same => small (same ▸ sourceBound)
    have nl : landing ≠ cell := fun same => small (same ▸ landingBound)
    simp [combined, change, small, ns, nl]

theorem combined_fill (separator : Nat) (state : State)
    (boxesUnique : state.boulders.Nodup) (holesUnique : state.holes.Nodup)
    (source hole : Cell) (sourceBound : source < separator) :
    combined separator {player := source, boulders := state.boulders.erase source, holes := state.holes.erase hole} =
      change (change (combined separator state) source none) (separator + hole) none := by
  funext cell
  by_cases small : cell < separator
  · have nt : separator + hole ≠ cell := by
      intro same
      exact Nat.not_le_of_lt small (same ▸ Nat.le_add_right separator hole)
    simpa [combined, small, project, change, nt] using congrFun (project_erase state.boulders boxesUnique source) cell
  · have ns : source ≠ cell := fun same => small (same ▸ sourceBound)
    have tagEq : (separator + hole = cell) ↔ (hole = cell - separator) := by
      simp only [Cell] at *
      omega
    simpa [combined, small, project, change, ns, tagEq] using congrFun (project_erase state.holes holesUnique hole) (cell - separator)

theorem matches_hero (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) : t.state.player = nextHero outcome := by
  cases outcome with
  | walk target => cases effect; rfl
  | push source result =>
    cases result with
    | stay landing => cases effect.2; rfl
    | fill hole => cases effect.2.2; rfl

theorem combined_matches (separator : Nat) (cells : List Cell) (bounds : ∀ cell ∈ cells, cell < separator)
    (state : State) (t : Transition) (outcome : Outcome)
    (boxesUnique : state.boulders.Nodup) (holesUnique : state.holes.Nodup)
    (before : state.boulders ⊆ cells) (after : t.state.boulders ⊆ cells)
    (effect : Matches state t outcome) :
    combined separator t.state = afterPattern separator (combined separator state) outcome := by
  cases outcome with
  | walk target => cases effect; rfl
  | push source result =>
    cases result with
    | stay landing =>
      rcases effect with ⟨present, shape⟩
      have sourceBound := bounds source (before present)
      have landingBound : landing < separator := by
        rw [shape] at after
        exact bounds landing (after List.mem_cons_self)
      subst t
      exact combined_stay separator state boxesUnique source landing sourceBound landingBound
    | fill hole =>
      rcases effect with ⟨present, hazard, shape⟩
      subst t
      exact combined_fill separator state boxesUnique holesUnique source hole (bounds source (before present))

theorem matches_delta (potential : Potential) (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) :
    potential.value state + slack potential outcome = Int.ofNat t.pushCost + potential.value t.state := by
  cases outcome with
  | walk target => cases effect; simp [slack, Transition.pushCost, Potential.value]
  | push source result =>
    cases result with
    | stay landing =>
      rcases effect with ⟨present, shape⟩
      have erased := weightSum_erase potential.boulder state.boulders source present
      subst t
      simp only [slack, Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one,
        Potential.value, weightSum]
      omega
    | fill hole =>
      rcases effect with ⟨present, hazard, shape⟩
      have boxesErased := weightSum_erase potential.boulder state.boulders source present
      have holesErased := weightSum_erase potential.hole state.holes hole hazard
      subst t
      simp only [slack, Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one,
        Potential.value]
      omega

end NetHack.Sokoban.HazardPattern
