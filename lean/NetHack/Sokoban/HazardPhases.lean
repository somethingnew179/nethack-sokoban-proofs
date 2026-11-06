/- Proved phase invariants for the unchanged individual-action model.
Finite static certificates may show that holes disappear in an exact order
and that players/boulders stay within phase-dependent regions. This is an
invariant of all traces, never an additional puzzle-profile restriction. -/
import NetHack.Sokoban.HazardPattern

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.HazardPhases
open PatternCorrection HazardPattern

def emptyBoxes : Pattern := fun _ => false

/-- A successful collision-free roll has the same endpoint after removing
all other boulders. Removing them can enable more actions, but never changes
the first hazard or the endpoint of a previously successful action. -/
theorem roll_empty_covers (board : Board) (b h : Pattern) (direction : Dir)
    (fuel current : Nat) (result : Ending)
    (checked : rollOracle board b h direction fuel current = some result) :
    rollOracle board emptyBoxes h direction fuel current = some result := by
  induction fuel generalizing current with
  | zero => simp [rollOracle] at checked
  | succ fuel ih =>
    cases adjacent : advance board current direction with
    | none => simpa [rollOracle, adjacent] using checked
    | some next =>
      cases door : board.doors.contains next <;>
        cases floor : board.floor.contains next <;>
        cases box : b next <;> cases hole : h next <;>
        simp only [rollOracle, adjacent, door, floor, box, hole, emptyBoxes,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at checked ⊢
      all_goals first | contradiction | exact checked | exact ih next checked

theorem push_empty_covers (board : Board) (b h : Pattern) (source : Cell)
    (direction : Dir) (result : Ending)
    (checked : pushOracle board b h source direction = some result) :
    pushOracle board emptyBoxes h source direction = some result := by
  have changeEmpty : change emptyBoxes source none = emptyBoxes := by
    funext cell
    simp [change, emptyBoxes]
  cases diagonal : direction.diagonal with
  | true => simp [pushOracle, diagonal] at checked
  | false =>
    cases behind : advance board source direction.opposite with
    | none => simp [pushOracle, diagonal, behind] at checked
    | some cell =>
      cases supportFloor : board.floor.contains cell <;>
        cases supportDoor : board.doors.contains cell <;>
        simp only [pushOracle, diagonal, Bool.false_eq_true, ↓reduceIte, bind,
          pure, Option.bind_some, behind, supportFloor, supportDoor,
          Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or] at checked ⊢
      all_goals first | contradiction | skip
      cases destination : advance board source direction with
      | none => simp [destination] at checked
      | some first =>
        cases floor : board.floor.contains first <;>
          cases door : board.doors.contains first <;> cases box : b first <;>
          cases hole : h first <;> cases rolling : board.rollingTraps.contains first <;>
          simp only [destination, Option.bind_some, floor, door, box, hole, rolling,
            emptyBoxes, changeEmpty, Bool.not_true, Bool.not_false, Bool.false_or,
            Bool.true_or, Bool.false_eq_true, ↓reduceIte] at checked ⊢
        all_goals first
          | contradiction
          | exact checked
          | exact roll_empty_covers board _ h direction _ source result checked

structure Certificate (board : Board) (original : List Cell) where
  heroes : Nat → List Cell
  crates : Nat → List Cell
  walk : ∀ phase, phase < original.length → ∀ hero ∈ heroes phase,
    ∀ direction target, advance board hero direction = some target →
    target ∈ board.floor → target ∉ original.drop phase → target ∈ heroes phase
  push : ∀ phase, phase < original.length → ∀ source ∈ crates phase,
    ∀ direction result,
    pushOracle board emptyBoxes (project (original.drop phase)) source direction = some result →
    match result with
    | .stay landing => source ∈ heroes phase ∧ landing ∈ crates phase
    | .fill hole => source ∈ heroes (phase + 1) ∧
      (original.drop phase).erase hole = original.drop (phase + 1) ∧
      crates phase ⊆ crates (phase + 1)

def At {board original} (cert : Certificate board original) (phase : Nat) (state : State) : Prop :=
  phase ≤ original.length ∧ state.holes = original.drop phase ∧
    state.player ∈ cert.heroes phase ∧ state.boulders ⊆ cert.crates phase

def Good {board original} (cert : Certificate board original) (state : State) : Prop :=
  state.boulders.Nodup ∧ ∃ phase, At cert phase state

theorem step_good {board original} (cert : Certificate board original)
    (state : State) (direction : Dir) (t : Transition) (good : Good cert state)
    (checked : step board state direction = some t) : Good cert t.state := by
  refine ⟨step_boulders_nodup _ _ _ _ good.1 checked, ?_⟩
  rcases good.2 with ⟨phase, bound, holes, hero, crates⟩
  have active : phase < original.length := by
    by_cases active : phase < original.length
    · exact active
    · have endPhase : phase = original.length := by omega
      have empty : state.holes = [] := by simpa [endPhase] using holes
      have stopped : step board state direction = none := by
        rcases state with ⟨player, boulders, remaining⟩
        cases empty
        cases standing : standingAllowed board ⟨player, boulders, []⟩ <;>
          simp only [step, standing, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some] <;> rfl
      rw [stopped] at checked
      contradiction
  rcases step_cases_full board state direction t checked with walk | pushed
  · rcases walk with ⟨target, adjacent, floor, _, clear, shape⟩
    refine ⟨phase, bound, ?_, ?_, ?_⟩
    · simpa [shape] using holes
    · simpa [shape] using cert.walk phase active state.player hero direction target
        adjacent floor (by simpa [← holes] using clear)
    · simpa [shape] using crates
  · rcases pushed with ⟨source, result, adjacent, floor, present, push, shape⟩
    have oracle := pushOracle_exact board state good.1 source direction
    rw [push, Option.map_some, holes] at oracle
    have empty := push_empty_covers board (project state.boulders)
      (project (original.drop phase)) source direction (ending result) oracle.symm
    have numeric := cert.push phase active source (crates present) direction (ending result) empty
    rcases (pushBoulder_spec board state source direction result push).1 with stay | fill
    · rcases stay with ⟨unfilled, resultBoxes⟩
      simp only [ending, unfilled] at numeric
      refine ⟨phase, bound, ?_, ?_, ?_⟩
      · simpa [shape, unfilled, afterFill] using holes
      · simpa [shape] using numeric.1
      · simp only [shape, resultBoxes]
        intro cell member
        rcases List.mem_cons.mp member with same | before
        · simpa [same] using numeric.2
        · exact crates (List.mem_of_mem_erase before)
    · rcases fill with ⟨filled, _, resultBoxes⟩
      simp only [ending, filled] at numeric
      refine ⟨phase + 1, by omega, ?_, ?_, ?_⟩
      · simpa [shape, filled, afterFill, holes] using numeric.2.1
      · simpa [shape] using numeric.1
      · simp only [shape, resultBoxes]
        intro cell member
        exact numeric.2.2 (crates (List.mem_of_mem_erase member))

theorem trace_good {board original} (cert : Certificate board original)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves) (initialGood : Good cert initial) :
    Good cert final := by
  induction trace with
  | nil => exact initialGood
  | cons head tail ih => exact ih (step_good cert _ _ _ initialGood head)

def walkCheck (board : Board) (original : List Cell) (heroes : Nat → List Cell)
    (phase : Nat) : Bool :=
  (heroes phase).all fun hero => allDirs.all fun direction =>
    match advance board hero direction with
    | none => true
    | some target => !board.floor.contains target ||
      (original.drop phase).contains target || (heroes phase).contains target

def pushCheck (board : Board) (original : List Cell) (heroes crates : Nat → List Cell)
    (phase : Nat) : Bool :=
  (crates phase).all fun source => allDirs.all fun direction =>
    match pushOracle board emptyBoxes (project (original.drop phase)) source direction with
    | none => true
    | some (.stay landing) => (heroes phase).contains source && (crates phase).contains landing
    | some (.fill hole) => (heroes (phase + 1)).contains source &&
      decide ((original.drop phase).erase hole = original.drop (phase + 1)) &&
      decide (crates phase ⊆ crates (phase + 1))

def ofChecks (board : Board) (original : List Cell) (heroes crates : Nat → List Cell)
    (walks : ∀ phase, phase < original.length → walkCheck board original heroes phase = true)
    (pushes : ∀ phase, phase < original.length → pushCheck board original heroes crates phase = true) :
    Certificate board original where
  heroes := heroes
  crates := crates
  walk := by
    intro phase active hero member direction target adjacent floor clear
    have row := List.all_eq_true.mp (List.all_eq_true.mp (walks phase active) hero member)
      direction (Geometry.all_directions direction)
    have absent : (original.drop phase).contains target = false := by simp [clear]
    simpa only [adjacent, List.contains_iff_mem.mpr floor, Bool.not_true,
      absent, Bool.false_or, List.contains_iff_mem] using row
  push := by
    intro phase active source member direction result checked
    have row := List.all_eq_true.mp (List.all_eq_true.mp (pushes phase active) source member)
      direction (Geometry.all_directions direction)
    cases result with
    | stay landing =>
      simpa only [checked, Bool.and_eq_true_iff, List.contains_iff_mem] using row
    | fill hole =>
      simpa only [checked, Bool.and_eq_true_iff, List.contains_iff_mem,
        decide_eq_true_eq, and_assoc] using row

end NetHack.Sokoban.HazardPhases
