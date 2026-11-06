/- An additive scalar for EACH actual boulder, depending on the actual hero
and the proved hole phase. The only abstraction is in certificate generation.
The theorem below quantifies over unchanged original Model Traces.
Single-boulder walk/own-push/phase inequalities must all be supplied as proofs.
No search result, initial assignment optimum, or actor reachability is assumed. -/
import NetHack.Sokoban.HeroPhasePotential.Projection

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.HeroPhasePotential
open LowerBounds HazardPattern
open HazardPhaseCountedCorrection (phaseOf nextPhase)

structure Certificate (board : Board) (original : List Cell)
    (phases : HazardPhases.Certificate board original) where
  weight : Nat → Cell → Cell → Int
  holeWeight : Cell → Int
  crate_disjoint : ∀ phase, phase ≤ original.length →
    ∀ box ∈ phases.crates phase, box ∉ original.drop phase
  walk : ∀ phase, phase < original.length →
    ∀ hero ∈ phases.heroes phase, ∀ box ∈ phases.crates phase,
    ∀ direction target,
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ≠ box →
    advance board hero direction = some target →
    target ∈ board.floor → target ∉ board.doors → target ∉ original.drop phase → target ≠ box →
    corner board (PatternCorrection.project [box]) hero direction = false →
    weight phase hero box ≤ weight phase target box
  push : ∀ phase, phase < original.length →
    ∀ hero ∈ phases.heroes phase, ∀ source ∈ phases.crates phase,
    ∀ direction result,
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ≠ source →
    source ∈ board.floor → source ∉ board.doors →
    advance board hero direction = some source →
    pushOracle board HazardPhases.emptyBoxes (PatternCorrection.project (original.drop phase))
      source direction = some result →
    match result with
    | .stay landing => weight phase hero source ≤ 1 + weight phase source landing
    | .fill hole => weight phase hero source + holeWeight hole ≤ 1
  advancePhase : ∀ phase, phase < original.length →
    ∀ hero ∈ board.floor, hero ∉ board.doors → hero ∉ original.drop phase →
    ∀ box ∈ phases.crates phase, box ∈ phases.crates (phase+1) → hero ≠ box →
    weight phase hero box ≤ weight (phase+1) hero box
  terminal : ∀ hero box, weight original.length hero box ≤ 0

def valueAt {board original phases} (cert : Certificate board original phases)
    (phase : Nat) (state : State) : Int :=
  weightSum (cert.weight phase state.player) state.boulders + weightSum cert.holeWeight state.holes

def value {board original phases} (cert : Certificate board original phases) (state : State) : Int :=
  valueAt cert (phaseOf original state) state

theorem step_bound {board original phases} (cert : Certificate board original phases)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state)
    (checked : step board state direction = some t) :
    value cert state ≤ Int.ofNat t.pushCost + value cert t.state := by
  rcases good with ⟨unique, phase, atIndex⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf original state) state := by
    rw [← phaseEq]
    exact atIndex
  let index := phaseOf original state
  have active : index < original.length :=
    HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have standing := step_player_clear board state direction t checked
  have heroHole : state.player ∉ original.drop index := by
    rw [← within.2.1]
    exact standing.2.2.2
  have clear : cornerBlocked board state direction = false :=
    FiniteTopology.step_corner_clear board state direction t checked
  have scalarWalk (box : Cell) (member : box ∈ state.boulders) (target : Cell)
      (adjacent : advance board state.player direction = some target)
      (floor : target ∈ board.floor) (door : target ∉ board.doors)
      (hole : target ∉ state.holes) (different : target ≠ box) :
      cert.weight index state.player box ≤ cert.weight index target box := by
    have heroBox : state.player ≠ box := by
      intro same
      apply standing.2.2.1
      simpa only [same] using member
    have targetHole : target ∉ original.drop index := by
      rw [← within.2.1]
      exact hole
    have smallCorner : corner board (PatternCorrection.project [box]) state.player direction = false :=
      (corner_project board (single state box) direction).trans
        (single_corner_clear board state box member direction clear)
    exact cert.walk index active state.player within.2.2.1 box (within.2.2.2 member)
      direction target standing.1 standing.2.1 heroHole heroBox adjacent floor door targetHole different smallCorner
  rcases step_cases_full board state direction t checked with walked | pushed
  · rcases walked with ⟨target, adjacent, floor, boxClear, holeClear, shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t target adjacent checked
    have mono := weightSum_mono state.boulders (cert.weight index state.player) (cert.weight index target)
      (fun box member => scalarWalk box member target adjacent floor door holeClear (by
        intro same
        apply boxClear
        simpa only [same] using member))
    have effect : Matches state t (.walk target) := shape
    have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within (.walk target) effect
    change phaseOf original t.state = index at afterPhase
    change valueAt cert index state ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state
    rw [afterPhase]
    simp only [valueAt, shape, Transition.pushCost, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    omega
  · rcases pushed with ⟨source, result, adjacent, floor, present, pushed, shape⟩
    have sourceInside := within.2.2.2 present
    have sourceHole : source ∉ original.drop index := cert.crate_disjoint index (by omega) source sourceInside
    have sourceHoleState : source ∉ state.holes := by
      rw [within.2.1]
      exact sourceHole
    have sourceDoor := FiniteTopology.step_target_not_door board state direction t source adjacent checked
    have heroSource : state.player ≠ source := by
      intro same
      apply standing.2.2.1
      simpa only [same] using present
    have exactOracle := pushOracle_exact board state unique source direction
    rw [pushed] at exactOracle
    have physical : pushOracle board (PatternCorrection.project state.boulders)
        (PatternCorrection.project state.holes) source direction = some (ending result) := by
      simpa only [Option.map_some] using exactOracle.symm
    have empty := HazardPhases.push_empty_covers board _ _ source direction _ physical
    rw [within.2.1] at empty
    have beforeBoxes := weightSum_erase (cert.weight index state.player) state.boulders source present
    rcases (pushBoulder_spec board state source direction result pushed).1 with stayed | filled
    · rcases stayed with ⟨notFilled, boxesShape⟩
      have emptyStay : pushOracle board HazardPhases.emptyBoxes
          (PatternCorrection.project (original.drop index)) source direction = some (.stay result.landing) := by
        simpa only [ending, notFilled] using empty
      have own := cert.push index active state.player within.2.2.1 source sourceInside
        direction (.stay result.landing) standing.1 standing.2.1 heroHole heroSource floor sourceDoor adjacent emptyStay
      have mono := weightSum_mono (state.boulders.erase source)
        (cert.weight index state.player) (cert.weight index source) (fun box member => by
          have erased := unique.mem_erase_iff.mp member
          exact scalarWalk box erased.2 source adjacent floor sourceDoor sourceHoleState erased.1.symm)
      have effect : Matches state t (.push source (.stay result.landing)) := by
        refine ⟨present, ?_⟩
        simpa only [notFilled, boxesShape, afterFill] using shape
      have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within
        (.push source (.stay result.landing)) effect
      change phaseOf original t.state = index at afterPhase
      change valueAt cert index state ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state
      rw [afterPhase]
      simp only [valueAt, effect.2, Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast, weightSum_cons]
      omega
    · rcases filled with ⟨hasFilled, hazard, boxesShape⟩
      have emptyFill : pushOracle board HazardPhases.emptyBoxes
          (PatternCorrection.project (original.drop index)) source direction = some (.fill result.landing) := by
        simpa only [ending, hasFilled] using empty
      have own := cert.push index active state.player within.2.2.1 source sourceInside
        direction (.fill result.landing) standing.1 standing.2.1 heroHole heroSource floor sourceDoor adjacent emptyFill
      have phaseInfo := phases.push index active source sourceInside direction (.fill result.landing) emptyFill
      have mono := weightSum_mono (state.boulders.erase source)
        (cert.weight index state.player) (cert.weight (index+1) source) (fun box member => by
          have erased := unique.mem_erase_iff.mp member
          have boxInside := within.2.2.2 erased.2
          have walked := scalarWalk box erased.2 source adjacent floor sourceDoor sourceHoleState erased.1.symm
          have advanced := cert.advancePhase index active source floor sourceDoor sourceHole
            box boxInside (phaseInfo.2.2 boxInside) erased.1.symm
          exact Int.le_trans walked advanced)
      have beforeHoles := weightSum_erase cert.holeWeight state.holes result.landing hazard
      have effect : Matches state t (.push source (.fill result.landing)) := by
        refine ⟨present, hazard, ?_⟩
        simpa only [hasFilled, boxesShape, afterFill] using shape
      have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within
        (.push source (.fill result.landing)) effect
      change phaseOf original t.state = index+1 at afterPhase
      change valueAt cert index state ≤ Int.ofNat t.pushCost + valueAt cert (phaseOf original t.state) t.state
      rw [afterPhase]
      simp only [valueAt, effect.2.2, Transition.pushCost, ↓reduceIte, Int.ofNat_eq_natCast]
      omega

theorem trace_bound {board original phases} (cert : Certificate board original phases)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (trace : Trace board initial directions final pushes moves)
    (initialGood : HazardPhases.Good phases initial) :
    value cert initial ≤ Int.ofNat pushes + value cert final := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    have localBound := step_bound cert _ _ _ initialGood head
    have nextGood := HazardPhases.step_good phases _ _ _ initialGood head
    have total := ih nextGood
    simp only [Int.ofNat_eq_natCast, Int.natCast_add] at localBound total ⊢
    omega

theorem goal_bound {board original phases} (cert : Certificate board original phases)
    (state : State) (completed : Goal state) : value cert state ≤ 0 := by
  have empty : state.holes = [] := completed
  have last : phaseOf original state = original.length := by simp only [phaseOf, empty, List.length_nil, Nat.sub_zero]
  have terminal := weightSum_nonpositive (cert.weight original.length state.player) state.boulders
    (cert.terminal state.player)
  simpa only [value, last, valueAt, empty, weightSum, Int.add_zero] using terminal

theorem pushes_lower_bound {board original phases} (cert : Certificate board original phases)
    {initial final : State} {directions : List Dir} {pushes moves : Nat}
    (initialGood : HazardPhases.Good phases initial) (cost : Nat)
    (initialValue : value cert initial = Int.ofNat cost)
    (trace : Trace board initial directions final pushes moves) (completed : Goal final) :
    cost ≤ pushes := by
  have total := trace_bound cert trace initialGood
  have terminal := goal_bound cert final completed
  rw [initialValue] at total
  simp only [Int.ofNat_eq_natCast] at total
  omega

end NetHack.Sokoban.HeroPhasePotential
