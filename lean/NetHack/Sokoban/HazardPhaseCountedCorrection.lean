/- Counted extension of HazardPhaseCorrection. Local cardinality is derived
from the unchanged Model invariant; it is not an extra premise on Trace.
The generic interface alone asserts no new numerical map bound. -/
/- Phase-aware correction certificates over proved invariants of Model.
Unlike a correction forced to vanish at every goal, the terminal inequality
may spend negative terminal potential. No phase or region is assumed of a
trace: HazardPhases proves their preservation from the actual initial state.
This supplies a certificate interface, not a new numerical map bound. -/
import NetHack.Sokoban.HazardPhases
import NetHack.Sokoban.PatternMass

set_option linter.unusedSimpArgs false
namespace NetHack.Sokoban.HazardPhaseCountedCorrection
open PatternCorrection HazardPattern HazardPhases LowerBounds

def phaseOf (original : List Cell) (state : State) : Nat := original.length - state.holes.length

theorem at_phase {board original} (phases : HazardPhases.Certificate board original)
    (index : Nat) (state : State) (atIndex : At phases index state) :
    index = phaseOf original state := by
  have size := congrArg List.length atIndex.2.1
  simp only [List.length_drop] at size
  unfold phaseOf
  have bound := atIndex.1
  omega

instance {board original} (phases : HazardPhases.Certificate board original)
    (index : Nat) (state : State) : Decidable (At phases index state) := by
  unfold At
  infer_instance

def Good {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (phases : HazardPhases.Certificate board original) (state : State) : Prop :=
  PatternCorrection.Good board original prior.allowance state ∧
    At phases (phaseOf original state) state

instance {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (phases : HazardPhases.Certificate board original) (state : State) :
    Decidable (Good prior phases state) := by unfold Good; infer_instance

def afterBoxes (p : Pattern) : Outcome → Pattern
  | .walk _ => p
  | .push source (.stay landing) => change p source (some landing)
  | .push source (.fill _) => change p source none

def nextPhase (index : Nat) : Outcome → Nat
  | .push _ (.fill _) => index + 1
  | _ => index

theorem boxes_project (cells : List Cell) (state : State) (subset : state.boulders ⊆ cells) :
    boxes cells (project state.boulders) = project state.boulders := by
  funext cell
  by_cases member : cell ∈ cells
  · simp [boxes, project, member]
  · have absent : cell ∉ state.boulders := fun h => member (subset h)
    simp [boxes, project, member, absent]

theorem matches_boxes (state : State) (t : Transition) (unique : state.boulders.Nodup)
    (outcome : Outcome) (effect : Matches state t outcome) :
    project t.state.boulders = afterBoxes (project state.boulders) outcome := by
  cases outcome with
  | walk target => cases effect; rfl
  | push source result =>
    cases result with
    | stay landing =>
      rw [effect.2]
      exact project_replace state.boulders unique source landing
    | fill hole =>
      rw [effect.2.2]
      exact project_erase state.boulders unique source

theorem matches_phase {board original} (phases : HazardPhases.Certificate board original)
    (state : State) (t : Transition) (within : At phases (phaseOf original state) state)
    (outcome : Outcome) (effect : Matches state t outcome) :
    phaseOf original t.state = nextPhase (phaseOf original state) outcome := by
  have length := congrArg List.length within.2.1
  simp only [List.length_drop] at length
  have holesBound : state.holes.length ≤ original.length := by omega
  cases outcome with
  | walk target => cases effect; rfl
  | push source result =>
    cases result with
    | stay landing => rw [effect.2]; rfl
    | fill hole =>
      have erased := List.length_erase_of_mem effect.2.1
      have positive := List.length_pos_of_mem effect.2.1
      rw [effect.2.2]
      simp only [phaseOf, nextPhase]
      change original.length - (state.holes.erase hole).length =
        original.length - state.holes.length + 1
      omega

theorem active_of_step {board original} (phases : HazardPhases.Certificate board original)
    (state : State) (within : At phases (phaseOf original state) state)
    (direction : Dir) (t : Transition) (checked : step board state direction = some t) :
    phaseOf original state < original.length := by
  by_cases active : phaseOf original state < original.length
  · exact active
  · have endPhase : phaseOf original state = original.length := by have := within.1; omega
    have empty : state.holes = [] := by simpa [endPhase] using within.2.1
    have stopped : step board state direction = none := by
      rcases state with ⟨player, boulders, remaining⟩
      cases empty
      cases standing : standingAllowed board ⟨player, boulders, []⟩ <;>
        simp only [step, standing, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ↓reduceIte, bind, pure, Option.bind_some] <;> rfl
    rw [stopped] at checked
    contradiction

theorem step_good {board original potential}
    (prior : PatternCorrection.Certificate board original potential)
    (phases : HazardPhases.Certificate board original)
    (state : State) (direction : Dir) (t : Transition) (good : Good prior phases state)
    (checked : step board state direction = some t) : Good prior phases t.state := by
  have reached := HazardPhases.step_good phases state direction t
    ⟨good.1.1, phaseOf original state, good.2⟩ checked
  rcases reached.2 with ⟨index, within⟩
  rw [at_phase phases index t.state within] at within
  exact ⟨PatternCorrection.step_good _ _ _ _ _ _ good.1 checked, within⟩

structure Certificate (board : Board) (original : List Cell) (potential : Potential)
    (prior : PatternCorrection.Certificate board original potential)
    (phases : HazardPhases.Certificate board original) where
  bonus : Nat → Cell → Pattern → Int
  nonnegative : ∀ index hero p, 0 ≤ bonus index hero p
  cratesUnique : ∀ index, (phases.crates index).Nodup
  localBound : ∀ index, index < original.length → ∀ hero ∈ phases.heroes index,
    ∀ direction p outcome,
    stepOracle board (boxes (phases.crates index) p) (project (original.drop index))
      hero direction = some outcome →
    ((phases.crates index).filter p).length ≤ (original.drop index).length + prior.allowance →
    bonus (nextPhase index outcome) (nextHero outcome) (afterBoxes p outcome) < bonus index hero p →
    prior.bonus hero p + bonus index hero p ≤ slack potential outcome +
      prior.bonus (nextHero outcome) (afterBoxes p outcome) +
      bonus (nextPhase index outcome) (nextHero outcome) (afterBoxes p outcome)
  goal : ∀ hero ∈ phases.heroes original.length, ∀ p,
    ((phases.crates original.length).filter p).length ≤ prior.allowance →
    prior.bonus hero p + bonus original.length hero p ≤
      weightSum (fun cell => -potential.boulder cell) ((phases.crates original.length).filter p)

def correction {board original potential prior phases}
    (cert : Certificate board original potential prior phases) (state : State) : Int :=
  if Good prior phases state then
    cert.bonus (phaseOf original state) state.player (project state.boulders) else 0

def value {board original potential prior phases}
    (cert : Certificate board original potential prior phases) (state : State) : Int :=
  PatternCorrection.value prior state + correction cert state

theorem correction_nonnegative {board original potential prior phases}
    (cert : Certificate board original potential prior phases) (state : State) :
    0 ≤ correction cert state := by
  unfold correction
  split
  · exact cert.nonnegative _ _ _
  · omega

theorem stepBound {board original potential prior phases}
    (cert : Certificate board original potential prior phases) (valid : Valid board potential) :
    StepBound board (value cert) := by
  intro state direction t checked
  have baseline := PatternCorrection.stepBound prior valid state direction t checked
  have afterNonnegative := correction_nonnegative cert t.state
  by_cases good : Good prior phases state
  · have nextGood := step_good prior phases state direction t good checked
    by_cases decreasing : cert.bonus (phaseOf original t.state) t.state.player (project t.state.boulders) <
        cert.bonus (phaseOf original state) state.player (project state.boulders)
    · rcases stepOracle_covers board state good.1.1 direction t checked with ⟨outcome, oracle, effect⟩
      have beforeBoxes := boxes_project _ state good.2.2.2.2
      have oracleExact : stepOracle board
          (boxes (phases.crates (phaseOf original state)) (project state.boulders))
          (project (original.drop (phaseOf original state))) state.player direction = some outcome := by
        rw [beforeBoxes, ← good.2.2.1]
        exact oracle
      have patternExact := matches_boxes state t good.1.1 outcome effect
      have phaseExact := matches_phase phases state t good.2 outcome effect
      have heroExact := matches_hero state t outcome effect
      have decreases : cert.bonus (nextPhase (phaseOf original state) outcome)
          (nextHero outcome) (afterBoxes (project state.boulders) outcome) <
          cert.bonus (phaseOf original state) state.player (project state.boulders) := by
        simpa only [← patternExact, ← phaseExact, ← heroExact] using decreasing
      have localBudget : ((phases.crates (phaseOf original state)).filter
          (project state.boulders)).length ≤
          (original.drop (phaseOf original state)).length + prior.allowance := by
        change PatternMass.mass (phases.crates (phaseOf original state))
          (project state.boulders) ≤ _
        rw [PatternMass.project_mass _ _ (cert.cratesUnique _) good.1.1 good.2.2.2.2]
        rw [← good.2.2.1]
        exact Nat.le_of_eq good.1.2.2.2
      have numeric := cert.localBound _ (active_of_step phases state good.2 direction t checked)
        state.player good.2.2.2.1 direction _ outcome oracleExact localBudget decreases
      rw [← patternExact, ← phaseExact, ← heroExact] at numeric
      have delta := matches_delta potential state t outcome effect
      simp only [value, correction, if_pos good, if_pos nextGood,
        PatternCorrection.value, PatternCorrection.correction, if_pos good.1, if_pos nextGood.1]
      omega
    · simp only [value, correction, if_pos good, if_pos nextGood]
      omega
  · simp only [value, correction, if_neg good]
    change PatternCorrection.value prior state + 0 ≤ Int.ofNat t.pushCost +
      (PatternCorrection.value prior t.state + correction cert t.state)
    omega

theorem goalBound {board original potential prior phases}
    (cert : Certificate board original potential prior phases) (valid : Valid board potential)
    (state : State) (completed : Goal state) : value cert state ≤ 0 := by
  by_cases good : Good prior phases state
  · have empty : state.holes = [] := completed
    have lastPhase : phaseOf original state = original.length := by simp [phaseOf, empty]
    have hero := good.2.2.2.1
    rw [lastPhase] at hero
    have occupiedLength := NonlinearFacts.occupied_length_le (phases.crates original.length)
      state.boulders (cert.cratesUnique original.length)
    have mass := good.1.2.2.2
    have budget : ((phases.crates original.length).filter (project state.boulders)).length ≤
        prior.allowance := by
      change (NonlinearFacts.occupied (phases.crates original.length) state.boulders).length ≤ prior.allowance
      simp only [empty, List.length_nil, Nat.zero_add] at mass
      omega
    have numeric := cert.goal state.player hero (project state.boulders) budget
    have selected := NonlinearFacts.occupied_weightSum_le (fun cell => -potential.boulder cell)
      (phases.crates original.length) state.boulders
      (fun cell => Int.neg_nonneg.mpr (valid.nonpositive cell)) (cert.cratesUnique original.length)
    have sumNeg (boxes : List Cell) : weightSum (fun cell => -potential.boulder cell) boxes =
        -weightSum potential.boulder boxes := by
      induction boxes with
      | nil => rfl
      | cons _ _ ih => simp only [weightSum, ih]; omega
    rw [sumNeg state.boulders] at selected
    change prior.bonus state.player (project state.boulders) +
      cert.bonus original.length state.player (project state.boulders) ≤
        weightSum (fun cell => -potential.boulder cell)
          (NonlinearFacts.occupied (phases.crates original.length) state.boulders) at numeric
    simp only [value, correction, if_pos good, lastPhase, PatternCorrection.value,
      PatternCorrection.correction, if_pos good.1, Potential.value, empty, weightSum, Int.add_zero]
    omega
  · have baseline := PatternCorrection.goalBound prior valid state completed
    simpa only [value, correction, if_neg good, Int.add_zero] using baseline

end NetHack.Sokoban.HazardPhaseCountedCorrection
