/- Strong one-step consequences of the SAME scalar certificate. These
lemmas expose already certified slack for sparse nonlinear corrections;
no action is removed and no solver reduction is assumed. -/
import NetHack.Sokoban.HeroPhasePotential.Core
namespace NetHack.Sokoban.HeroPhasePotential
open LowerBounds HazardPattern
open HazardPhaseCountedCorrection (phaseOf)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem step_target (board : Board) (state : State) (direction : Dir) (t : Transition)
    (checked : step board state direction = some t) :
    advance board state.player direction = some t.state.player ∧
      t.state.player ∈ board.floor ∧ t.state.player ∉ board.doors := by
  rcases step_cases_full board state direction t checked with walked | pushed
  · rcases walked with ⟨target, adjacent, floor, _, _, shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t target adjacent checked
    simpa only [shape] using And.intro adjacent (And.intro floor door)
  · rcases pushed with ⟨source, result, adjacent, floor, _, _, shape⟩
    have door := FiniteTopology.step_target_not_door board state direction t source adjacent checked
    simpa only [shape] using And.intro adjacent (And.intro floor door)

theorem strict_stay {board original phases} (cert : Certificate board original phases)
    (state : State) (direction : Dir) (t : Transition)
    (good : HazardPhases.Good phases state)
    (checked : step board state direction = some t)
    (source landing : Cell) (effect : Matches state t (.push source (.stay landing)))
    (strictOwn : cert.weight (phaseOf original state) state.player source ≤
      cert.weight (phaseOf original state) source landing) : value cert state ≤ value cert t.state := by
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

  have present := effect.1
  have target := step_target board state direction t checked
  have adjacent : advance board state.player direction = some source := by simpa only [effect.2] using target.1
  have floor : source ∈ board.floor := by simpa only [effect.2] using target.2.1
  have door : source ∉ board.doors := by simpa only [effect.2] using target.2.2
  have noHole : source ∉ state.holes := by
    rw [within.2.1]
    exact cert.crate_disjoint index (by omega) source (within.2.2.2 present)
  have before := weightSum_erase (cert.weight index state.player) state.boulders source present
  have mono := weightSum_mono (state.boulders.erase source)
    (cert.weight index state.player) (cert.weight index source) (fun box member => by
      have erased := unique.mem_erase_iff.mp member
      exact scalarWalk box erased.2 source adjacent floor door noHole erased.1.symm)
  have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within
    (.push source (.stay landing)) effect
  change phaseOf original t.state = index at afterPhase
  change cert.weight index state.player source ≤ cert.weight index source landing at strictOwn
  change valueAt cert index state ≤ valueAt cert (phaseOf original t.state) t.state
  rw [afterPhase]
  simp only [valueAt, effect.2, weightSum_cons]
  omega

/-- An unconsumed negative-weight witness pays at least one unit of slack
at the last fill. This lemma uses exact list sums, not a state-count search. -/
theorem last_fill_before_nonpositive {board original phases}
    (cert : Certificate board original phases) (phase : Nat) (state : State)
    (source hole witness : Cell) (onlyHole : state.holes = [hole])
    (present : source ∈ state.boulders) (retained : witness ∈ state.boulders.erase source)
    (nonpositive : ∀ box, cert.weight phase state.player box ≤ 0)
    (negative : cert.weight phase state.player witness ≤ -1)
    (own : cert.weight phase state.player source + cert.holeWeight hole ≤ 1) :
    valueAt cert phase state ≤ 0 := by
  have a := weightSum_erase (cert.weight phase state.player) state.boulders source present
  have b := weightSum_erase (cert.weight phase state.player) (state.boulders.erase source) witness retained
  have c := weightSum_nonpositive (cert.weight phase state.player)
    ((state.boulders.erase source).erase witness) nonpositive
  simp only [valueAt, onlyHole, weightSum_cons, weightSum, Int.add_zero]
  omega
end NetHack.Sokoban.HeroPhasePotential
