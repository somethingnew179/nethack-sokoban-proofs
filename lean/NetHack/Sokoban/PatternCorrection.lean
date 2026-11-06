/- Occupancy certificates over the unchanged individual-action model.
Patterns are arbitrary Boolean functions, not solver states. All reductions
below cover every admitted model transition; finite inequalities are supplied
as ordinary Lean proofs. -/
import NetHack.Sokoban.PreciseRolling
import NetHack.Sokoban.NonlinearFacts

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.PatternCorrection
open LowerBounds
abbrev Pattern := Cell → Bool

def project (boxes : List Cell) : Pattern := boxes.contains

def change (pattern : Pattern) (source : Cell) (destination : Option Cell) : Pattern :=
  fun cell => if destination = some cell then true else if source = cell then false else pattern cell

theorem project_erase (boxes : List Cell) (unique : boxes.Nodup) (source : Cell) :
    project (boxes.erase source) = change (project boxes) source none := by
  funext cell
  apply Bool.eq_iff_iff.mpr
  simp only [project, change, List.contains_iff_mem, Option.noConfusion, ↓reduceIte]
  rw [unique.mem_erase_iff]
  by_cases same : source = cell <;> simp_all [Ne.symm]

theorem project_replace (boxes : List Cell) (unique : boxes.Nodup) (source destination : Cell) :
    project (destination :: boxes.erase source) = change (project boxes) source (some destination) := by
  funext cell
  by_cases hd : destination = cell <;> by_cases hs : source = cell <;>
    simp [project, change, hd, hs, Ne.symm, unique.mem_erase_iff]

def known (support : List Cell) (pattern : Pattern) (cell : Cell) : Bool :=
  support.contains cell && pattern cell

def relaxedBlocked (board : Board) (support : List Cell) (pattern : Pattern) (cell : Cell) : Bool :=
  (!board.floor.contains cell && !board.doors.contains cell) || known support pattern cell

def relaxedSide (board : Board) (support : List Cell) (pattern : Pattern)
    (player : Cell) (direction : Dir) : Bool :=
  match advance board player direction with
  | none => true
  | some cell => relaxedBlocked board support pattern cell

def relaxedCorner (board : Board) (support : List Cell) (pattern : Pattern)
    (player : Cell) (direction : Dir) : Bool :=
  direction.diagonal && relaxedSide board support pattern player direction.sides.1 &&
    relaxedSide board support pattern player direction.sides.2

def walkGuard (board : Board) (support : List Cell) (pattern : Pattern)
    (player target : Cell) (direction : Dir) : Bool :=
  !known support pattern player && !known support pattern target &&
    !relaxedCorner board support pattern player direction

def pushGuard (support : List Cell) (pattern : Pattern) (player source first landing : Cell) : Bool :=
  !known support pattern player && (!support.contains source || known support pattern source) &&
    !known support pattern first && (!known support pattern landing || decide (landing = source))

private theorem known_clear (support boxes : List Cell) (cell : Cell) (clear : cell ∉ boxes) :
    known support (project boxes) cell = false := by simp [known, project, clear]

private theorem corner_clear (board : Board) (support : List Cell) (state : State) (direction : Dir)
    (clear : cornerBlocked board state direction = false) :
    relaxedCorner board support (project state.boulders) state.player direction = false := by
  have blocked_imp (cell : Cell)
      (h : relaxedBlocked board support (project state.boulders) cell = true) :
      blocked board state cell = true := by
    rcases Bool.or_eq_true_iff.mp h with wall | box
    · exact Bool.or_eq_true_iff.mpr (Or.inl wall)
    · exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mp box).2)
  have side_imp (d : Dir)
      (h : relaxedSide board support (project state.boulders) state.player d = true) :
      (match advance board state.player d with | none => true | some c => blocked board state c) = true := by
    cases adjacent : advance board state.player d with
    | none => rfl
    | some cell =>
      simp only [relaxedSide, adjacent] at h
      exact blocked_imp cell h
  cases corner : relaxedCorner board support (project state.boulders) state.player direction with
  | false => rfl
  | true =>
    rcases Bool.and_eq_true_iff.mp corner with ⟨left, second⟩
    rcases Bool.and_eq_true_iff.mp left with ⟨diagonal, first⟩
    have actual : cornerBlocked board state direction = true := by
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨diagonal, side_imp _ first⟩, side_imp _ second⟩
    simp [clear] at actual

private theorem step_corner_clear (board : Board) (state : State) (direction : Dir) (t : Transition)
    (checked : step board state direction = some t) : cornerBlocked board state direction = false := by
  let rawCore (board : Board) (state : State) (direction : Dir) : Option Transition := do
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
  have core : rawCore board state direction = some t := step_core_of _ _ _ _ checked
  cases corner : cornerBlocked board state direction with
  | false => rfl
  | true =>
    cases completed : goal state <;> cases adjacent : advance board state.player direction <;>
      simp [rawCore, corner, completed, adjacent] at core

structure Certificate (board : Board) (originalHoles : List Cell) (potential : Potential) where
  allowance : Nat
  support : List Cell
  unique : support.Nodup
  bonus : Cell → Pattern → Int
  nonnegative : ∀ player pattern, 0 ≤ bonus player pattern
  walk : ∀ player, player ∈ board.floor → ∀ direction target,
    advance board player direction = some target → target ∈ board.floor → ∀ pattern,
    walkGuard board support pattern player target direction = true → bonus player pattern ≤ bonus target pattern
  stay : ∀ player, player ∈ board.floor → ∀ direction source first landing,
    direction.diagonal = false → advance board player direction = some source → source ∈ board.floor →
    advance board source direction = some first → first ∈ board.floor →
    landing ∈ PreciseRolling.stayTargets board source direction → ∀ pattern,
    pushGuard support pattern player source first landing = true →
    bonus player pattern ≤ 1 + potential.boulder landing - potential.boulder source +
      bonus source (change pattern source (some landing))
  consume : ∀ player, player ∈ board.floor → ∀ direction source first landing,
    direction.diagonal = false → advance board player direction = some source → source ∈ board.floor →
    advance board source direction = some first → first ∈ board.floor →
    landing ∈ pushTargets board source direction → landing ∈ originalHoles → ∀ pattern,
    pushGuard support pattern player source first landing = true →
    bonus player pattern ≤ 1 - potential.boulder source - potential.hole landing +
      bonus source (change pattern source none)
  goal : ∀ player pattern, (support.filter pattern).length ≤ allowance →
    bonus player pattern ≤ weightSum (fun cell => -potential.boulder cell) (support.filter pattern)

def Good (board : Board) (originalHoles : List Cell) (allowance : Nat) (state : State) : Prop :=
  state.boulders.Nodup ∧ state.holes ⊆ originalHoles ∧ state.player ∈ board.floor ∧ state.boulders.length = state.holes.length + allowance
instance (board : Board) (originalHoles : List Cell) (allowance : Nat) (state : State) :
    Decidable (Good board originalHoles allowance state) := by unfold Good; infer_instance

def correction {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (state : State) : Int :=
  if Good board originalHoles cert.allowance state then cert.bonus state.player (project state.boulders) else 0

def value {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (state : State) : Int := potential.value state + correction cert state

theorem step_good (board : Board) (originalHoles : List Cell) (allowance : Nat) (state : State) (direction : Dir) (t : Transition)
    (good : Good board originalHoles allowance state) (checked : step board state direction = some t) :
    Good board originalHoles allowance t.state := by
  refine ⟨step_boulders_nodup _ _ _ _ good.1 checked,
    fun _ h => good.2.1 ((step_holes_sublist _ _ _ _ checked).subset h),
    step_player_floor _ _ _ _ checked, ?_⟩
  have conserved := step_conservation _ _ _ _ checked
  have mass := good.2.2.2
  omega

theorem stepBound {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (valid : Valid board potential) : StepBound board (value cert) := by
  intro state direction t checked
  by_cases good : Good board originalHoles cert.allowance state
  · have nextGood := step_good _ _ _ _ _ _ good checked
    have playerClear := (step_player_clear _ _ _ _ checked).2.2.1
    have clear := known_clear cert.support state.boulders state.player playerClear
    have bound : potential.value state + cert.bonus state.player (project state.boulders) ≤
        Int.ofNat t.pushCost + potential.value t.state + cert.bonus t.state.player (project t.state.boulders) := by
      rcases step_cases_full _ _ _ _ checked with walk | pushed
      · rcases walk with ⟨target, adjacent, targetFloor, targetClear, _, shape⟩
        have corner := corner_clear board cert.support state direction (step_corner_clear _ _ _ _ checked)
        have targetKnown := known_clear cert.support state.boulders target targetClear
        have guard : walkGuard board cert.support (project state.boulders) state.player target direction = true := by
          simp only [walkGuard, clear, targetKnown, corner, Bool.not_false, Bool.true_and]
        have numeric := cert.walk state.player good.2.2.1 direction target adjacent targetFloor _ guard
        subst t
        simpa only [Transition.pushCost, Bool.false_eq_true, ↓reduceIte, Int.ofNat_zero,
          Int.zero_add, Int.ofNat_eq_natCast, Potential.value, Int.add_le_add_iff_left] using Int.add_le_add_left numeric (potential.value state)
      · rcases pushed with ⟨source, result, adjacent, sourceFloor, present, pushed, shape⟩
        have diagonal : direction.diagonal = false := by
          cases hd : direction.diagonal with
          | false => rfl
          | true => simp [pushBoulder, hd] at pushed
        rcases NonlinearFacts.pushBoulder_first_clear _ _ _ _ _ pushed with
          ⟨first, firstAdj, firstFloor, _, firstClear⟩
        have firstKnown := known_clear cert.support state.boulders first firstClear
        have sourceGuard : (!cert.support.contains source || known cert.support (project state.boulders) source) = true := by
          simp [known, project, present]
        have landing : (!known cert.support (project state.boulders) result.landing || decide (result.landing = source)) = true := by
          rcases NonlinearFacts.pushBoulder_landing_old_clear_or_source _ _ _ _ _ pushed with same | fresh
          · simp [same]
          · simp [known_clear cert.support state.boulders result.landing fresh]
        have guard : pushGuard cert.support (project state.boulders) state.player source first result.landing = true := by
          simp only [pushGuard, clear, Bool.not_false, Bool.true_and, sourceGuard, firstKnown, landing, Bool.and_true]
        have boxes := weightSum_erase potential.boulder state.boulders source present
        rcases (pushBoulder_spec _ _ _ _ _ pushed).1 with stays | consumes
        · rcases stays with ⟨unfilled, resultBoxes⟩
          have numeric := cert.stay state.player good.2.2.1 direction source first result.landing
            diagonal adjacent sourceFloor firstAdj firstFloor
            (PreciseRolling.push_no_fill_target _ _ _ _ _ pushed unfilled) _ guard
          rw [← project_replace state.boulders good.1 source result.landing, ← resultBoxes] at numeric
          subst t
          simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one, unfilled, afterFill,
            Potential.value, resultBoxes, weightSum] at numeric ⊢
          omega
        · rcases consumes with ⟨filled, hazard, resultBoxes⟩
          have numeric := cert.consume state.player good.2.2.1 direction source first result.landing
            diagonal adjacent sourceFloor firstAdj firstFloor (pushBoulder_spec _ _ _ _ _ pushed).2
            (good.2.1 hazard) _ guard
          rw [← project_erase state.boulders good.1 source, ← resultBoxes] at numeric
          have holes := weightSum_erase potential.hole state.holes result.landing hazard
          subst t
          simp only [Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one, filled, afterFill,
            Potential.value, resultBoxes] at numeric ⊢
          omega
    simpa only [value, correction, if_pos good, if_pos nextGood, Int.add_assoc] using bound
  · have base := valid.stepBound state direction t checked
    have nonnegative : 0 ≤ correction cert t.state := by
      unfold correction
      split
      · exact cert.nonnegative _ _
      · omega
    simp only [value, correction, if_neg good]
    change potential.value state + 0 ≤ Int.ofNat t.pushCost +
      (potential.value t.state + correction cert t.state)
    omega

theorem goalBound {board originalHoles potential} (cert : Certificate board originalHoles potential)
    (valid : Valid board potential) (state : State) (completed : Goal state) : value cert state ≤ 0 := by
  by_cases good : Good board originalHoles cert.allowance state
  · have selectedLength := NonlinearFacts.occupied_length_le cert.support state.boulders cert.unique
    have mass := good.2.2.2
    have holesEmpty : state.holes = [] := completed
    have budget : (cert.support.filter (project state.boulders)).length ≤ cert.allowance := by
      change (NonlinearFacts.occupied cert.support state.boulders).length ≤ cert.allowance
      simp only [holesEmpty, List.length_nil, Nat.zero_add] at mass
      omega
    have numeric := cert.goal state.player (project state.boulders) budget
    have selected := NonlinearFacts.occupied_weightSum_le (fun cell => -potential.boulder cell)
      cert.support state.boulders (fun cell => Int.neg_nonneg.mpr (valid.nonpositive cell)) cert.unique
    have sumNeg (boxes : List Cell) : weightSum (fun cell => -potential.boulder cell) boxes =
        -weightSum potential.boulder boxes := by
      induction boxes with
      | nil => rfl
      | cons _ _ ih => simp only [weightSum, ih]; omega
    rw [sumNeg state.boulders] at selected
    change state.holes = [] at completed
    simp only [value, correction, if_pos good, Potential.value, completed, weightSum, Int.add_zero]
    change _ ≤ _ at selected
    change cert.bonus state.player (project state.boulders) ≤
      weightSum (fun cell => -potential.boulder cell) (NonlinearFacts.occupied cert.support state.boulders) at numeric
    omega
  · simpa only [value, correction, if_neg good, Int.add_zero] using valid.goalBound state completed
end NetHack.Sokoban.PatternCorrection
