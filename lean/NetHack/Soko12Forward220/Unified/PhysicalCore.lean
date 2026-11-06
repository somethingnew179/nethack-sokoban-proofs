import NetHack.Soko12Forward220.Shared.OldBridge
import NetHack.Sokoban.CountedLocalCase
import NetHack.SokobanLinearPhases.Map12.Invariant
import NetHack.Sokoban.HazardPhaseCountedCorrection
import NetHack.Sokoban.Generated.Soko31Potential
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

structure PhysicalCase where
  phase : Nat
  hero : Cell
  direction : Dir
  outcome : Outcome
  frame : CountedLocalCase.Frame

def changesFor : Outcome → DecisionDAGTransform.Bindings
  | .walk _ => []
  | .push source (.stay landing) => [(landing, true), (source, false)]
  | .push source (.fill _) => [(source, false)]

def gammaAfter (phase : Nat) (outcome : Outcome) : Nat :=
  Shared.gamma (HazardPhaseCountedCorrection.nextPhase phase outcome) (nextHero outcome)

def budgetFor (phase : Nat) : Outcome → Int
  | .walk _ => Int.ofNat (20-phase)
  | .push source _ => Int.ofNat (20-phase) - (if source ∈ Shared.cells then 0 else 1)

def fits (c : PhysicalCase) : Bool :=
  decide (c.frame.beforeBeta = Shared.oldRoot c.hero ∧ c.frame.beforeBonus = Shared.gamma c.phase c.hero ∧
    c.frame.afterBeta = Shared.oldRoot (nextHero c.outcome) ∧ c.frame.afterBonus = gammaAfter c.phase c.outcome ∧
    c.frame.changes = changesFor c.outcome ∧ c.frame.budget = budgetFor c.phase c.outcome ∧
    c.frame.slack = slack Generated.soko1_2Potential c.outcome ∧
    c.hero ∈ soko1_2.board.floor ∧ nextHero c.outcome ∈ soko1_2.board.floor)

theorem changesFor_exact (p : PatternCorrection.Pattern) (outcome : Outcome) :
    HazardPhaseCountedCorrection.afterBoxes p outcome = DecisionDAGTransform.update p (changesFor outcome) := by
  cases outcome with
  | walk hero => rfl
  | push source ending =>
    cases ending with
    | stay landing =>
      funext cell
      by_cases dest : landing = cell <;> by_cases origin : source = cell <;>
        simp [HazardPhaseCountedCorrection.afterBoxes, changesFor, PatternCorrection.change,
          DecisionDAGTransform.update, DecisionDAGTransform.lookup, dest, origin]
    | fill hole =>
      funext cell
      by_cases origin : source = cell <;>
        simp [HazardPhaseCountedCorrection.afterBoxes, changesFor, PatternCorrection.change,
          DecisionDAGTransform.update, DecisionDAGTransform.lookup, origin]

theorem case_sound (system : CountedLocalCase.System)
    (reader : system.read = Shared.read) (support : system.support = Shared.cells)
    (c : PhysicalCase) (fitted : fits c = true)
    (valid : CountedLocalCase.Holds system c.frame) (p : PatternCorrection.Pattern)
    (satisfied : DecisionDAGTransform.Satisfies c.frame.bindings p)
    (budget : DecisionDAGCountedCompact.count Shared.cells p ≤ budgetFor c.phase c.outcome)
    (decreasing : DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p c.outcome)
        (gammaAfter c.phase c.outcome) < DecisionDAG.eval Shared.read p (Shared.gamma c.phase c.hero)) :
    NetHack.Sokoban12CostPartition.bonus c.hero p + DecisionDAG.eval Shared.read p (Shared.gamma c.phase c.hero) ≤
      slack Generated.soko1_2Potential c.outcome +
      NetHack.Sokoban12CostPartition.bonus (nextHero c.outcome)
        (HazardPhaseCountedCorrection.afterBoxes p c.outcome) +
      DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p c.outcome) (gammaAfter c.phase c.outcome) := by
  have facts : c.frame.beforeBeta = Shared.oldRoot c.hero ∧ c.frame.beforeBonus = Shared.gamma c.phase c.hero ∧
      c.frame.afterBeta = Shared.oldRoot (nextHero c.outcome) ∧ c.frame.afterBonus = gammaAfter c.phase c.outcome ∧
      c.frame.changes = changesFor c.outcome ∧ c.frame.budget = budgetFor c.phase c.outcome ∧
      c.frame.slack = slack Generated.soko1_2Potential c.outcome ∧
      c.hero ∈ soko1_2.board.floor ∧ nextHero c.outcome ∈ soko1_2.board.floor := of_decide_eq_true fitted
  have after : DecisionDAGTransform.update p c.frame.changes =
      HazardPhaseCountedCorrection.afterBoxes p c.outcome := by
    rw [facts.2.2.2.2.1]
    exact (changesFor_exact p c.outcome).symm
  have validBudget : DecisionDAGCountedCompact.count system.support p ≤ c.frame.budget := by
    simpa only [support, facts.2.2.2.2.2.1] using budget
  have validDecrease : DecisionDAG.eval system.read (DecisionDAGTransform.update p c.frame.changes)
        c.frame.afterBonus < DecisionDAG.eval system.read p c.frame.beforeBonus := by
    simpa only [reader, after, facts.2.1, facts.2.2.2.1] using decreasing
  have result := valid p satisfied validBudget validDecrease
  rw [reader] at result
  change DecisionDAG.eval Shared.read p c.frame.beforeBeta + DecisionDAG.eval Shared.read p c.frame.beforeBonus ≤
    c.frame.slack + DecisionDAG.eval Shared.read (DecisionDAGTransform.update p c.frame.changes) c.frame.afterBeta +
      DecisionDAG.eval Shared.read (DecisionDAGTransform.update p c.frame.changes) c.frame.afterBonus at result
  rw [facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.2.2.1, after,
    Shared.old_bonus_matches c.hero facts.2.2.2.2.2.2.2.1 p,
    Shared.old_bonus_matches (nextHero c.outcome) facts.2.2.2.2.2.2.2.2
      (HazardPhaseCountedCorrection.afterBoxes p c.outcome)] at result
  exact result


theorem tracked_unique : Shared.cells.Nodup := by decide +kernel
theorem tracked_subset (phase : Nat) (active : phase < 18) : Shared.cells ⊆ NetHack.SokobanLinearPhases.Map12.crates phase := by
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 ∨ phase = 15 ∨ phase = 16 ∨ phase = 17 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem budget_of_oracle (phase : Nat) (active : phase < 18) (p : PatternCorrection.Pattern) (hero : Cell) (direction : Dir)
    (outcome : Outcome)
    (mass : PatternMass.mass (NetHack.SokobanLinearPhases.Map12.crates phase) p ≤ 20-phase)
    (checked : stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
      (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction = some outcome) :
    DecisionDAGCountedCompact.count Shared.cells p ≤ budgetFor phase outcome := by
  have mono := PatternMass.mass_mono Shared.cells (NetHack.SokobanLinearPhases.Map12.crates phase) p
    tracked_unique (tracked_subset phase active)
  rw [CountedLocalCase.count_eq_mass]
  simp only [Int.ofNat_eq_natCast]
  cases outcome with
  | walk target =>
    change (PatternMass.mass Shared.cells p : Int) ≤ Int.ofNat (20-phase)
    simp only [Int.ofNat_eq_natCast]
    omega
  | push source ending =>
    by_cases tracked : source ∈ Shared.cells
    · simp only [budgetFor, if_pos tracked, Int.sub_zero, Int.ofNat_eq_natCast]
      omega
    · have occupied := CountedLocalCase.oracle_push_source soko1_2.board
        (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
        (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction source ending checked
      have selected : source ∈ NetHack.SokobanLinearPhases.Map12.crates phase ∧ p source = true := by
        simpa [boxes] using occupied
      have extra := PatternMass.mass_extra Shared.cells (NetHack.SokobanLinearPhases.Map12.crates phase) p
        tracked_unique (tracked_subset phase active) source selected.1 selected.2 tracked
      simp only [budgetFor, if_neg tracked, Int.ofNat_eq_natCast]
      omega
def OracleCovered (entries : List PhysicalCase) (p : PatternCorrection.Pattern) (outcome : Outcome) : Prop :=
  ∃ entry ∈ entries, outcome = entry.outcome ∧ DecisionDAGTransform.Satisfies entry.frame.bindings p

def LocalBoundFor (phase : Nat) (hero : Cell) (direction : Dir) : Prop :=
  ∀ p outcome,
    stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
      (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction = some outcome →
    PatternMass.mass (NetHack.SokobanLinearPhases.Map12.crates phase) p ≤ 20-phase →
    DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p outcome) (gammaAfter phase outcome) <
      DecisionDAG.eval Shared.read p (Shared.gamma phase hero) →
    NetHack.Sokoban12CostPartition.bonus hero p + DecisionDAG.eval Shared.read p (Shared.gamma phase hero) ≤
      slack Generated.soko1_2Potential outcome +
      NetHack.Sokoban12CostPartition.bonus (nextHero outcome)
        (HazardPhaseCountedCorrection.afterBoxes p outcome) +
      DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p outcome) (gammaAfter phase outcome)

theorem combine_row (system : CountedLocalCase.System)
    (reader : system.read = Shared.read) (support : system.support = Shared.cells)
    (phase : Nat) (active : phase < 18) (hero : Cell) (direction : Dir) (entries : List PhysicalCase)
    (covered : ∀ p outcome,
      stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
        (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction = some outcome →
      OracleCovered entries p outcome)
    (fitted : ∀ entry ∈ entries, fits entry = true)
    (valid : ∀ entry ∈ entries, CountedLocalCase.Holds system entry.frame)
    (heroes : ∀ entry ∈ entries, entry.hero = hero)
    (phases : ∀ entry ∈ entries, entry.phase = phase) : LocalBoundFor phase hero direction := by
  intro p outcome checked mass decreasing
  rcases covered p outcome checked with ⟨entry, member, same, satisfied⟩
  have budget := budget_of_oracle phase active p hero direction outcome mass checked
  have entryBudget : DecisionDAGCountedCompact.count Shared.cells p ≤ budgetFor entry.phase entry.outcome := by
    simpa only [← same, phases entry member] using budget
  have entryDecrease :
      DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p entry.outcome)
          (gammaAfter entry.phase entry.outcome) < DecisionDAG.eval Shared.read p (Shared.gamma entry.phase entry.hero) := by
    simpa only [← same, heroes entry member, phases entry member] using decreasing
  have result := case_sound system reader support entry (fitted entry member) (valid entry member) p satisfied
    entryBudget entryDecrease
  simpa only [← same, heroes entry member, phases entry member] using result
end NetHack.Soko12Forward220.Unified
