/- Physical coverage of the exact original oracle, independent of table validity.
The data checker is related to the proof-carrying checker by a kernel-proved
rfl theorem. Numeric inequalities are obtained ONLY from a genuine System. -/
import NetHack.Soko12Forward220.Unified.RawData
namespace NetHack.Soko12Forward220.Unified
open NetHack.Sokoban NetHack.Sokoban.HazardPattern

def CoveredFor (phase : Nat) (hero : Cell) (direction : Dir) : Prop :=
  ∀ p outcome,
    stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
      (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction = some outcome →
    ∃ entry : PhysicalCase,
      entry.phase = phase ∧ entry.hero = hero ∧ entry.direction = direction ∧
      fits entry = true ∧ CountedLocalCaseData.check data entry.frame = true ∧
      outcome = entry.outcome ∧ DecisionDAGTransform.Satisfies entry.frame.bindings p

theorem row_covered (phase : Nat) (hero : Cell) (direction : Dir) (entries : List PhysicalCase)
    (covered : ∀ p outcome,
      stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
        (PatternCorrection.project (soko1_2.initial.holes.drop phase)) hero direction = some outcome →
      OracleCovered entries p outcome)
    (fitted : ∀ entry ∈ entries, fits entry = true)
    (checked : ∀ entry ∈ entries, CountedLocalCaseData.check data entry.frame = true)
    (heroes : ∀ entry ∈ entries, entry.hero = hero)
    (directions : ∀ entry ∈ entries, entry.direction = direction)
    (phases : ∀ entry ∈ entries, entry.phase = phase) : CoveredFor phase hero direction := by
  intro p outcome oracle
  rcases covered p outcome oracle with ⟨entry,member,same,satisfied⟩
  exact ⟨entry,phases entry member,heroes entry member,directions entry member,
    fitted entry member,checked entry member,same,satisfied⟩

/-- This implication still explicitly needs all semantic proof fields of System.
Physical coverage/raw matching alone is never promoted to a numeric bound. -/
theorem local_of_covered (sys : CountedLocalCase.System)
    (sameData : CountedLocalCaseData.fromSystem sys = data)
    (phase : Nat) (active : phase < 18) (hero : Cell) (direction : Dir)
    (covered : CoveredFor phase hero direction) : LocalBoundFor phase hero direction := by
  intro p outcome oracle mass decreasing
  rcases covered p outcome oracle with ⟨entry,phaseExact,heroExact,_,fitted,checked,same,satisfied⟩
  have reader : sys.read = Shared.read := congrArg CountedLocalCaseData.Data.read sameData
  have support : sys.support = Shared.cells := congrArg CountedLocalCaseData.Data.support sameData
  have valid := CountedLocalCaseData.checked_sound sys data sameData entry.frame checked
  have budget := budget_of_oracle phase active p hero direction outcome mass oracle
  have entryBudget : DecisionDAGCountedCompact.count Shared.cells p ≤ budgetFor entry.phase entry.outcome := by
    simpa only [phaseExact,←same] using budget
  have entryDecreasing :
      DecisionDAG.eval Shared.read (HazardPhaseCountedCorrection.afterBoxes p entry.outcome)
        (gammaAfter entry.phase entry.outcome) <
      DecisionDAG.eval Shared.read p (Shared.gamma entry.phase entry.hero) := by
    simpa only [phaseExact,heroExact,←same] using decreasing
  have result := case_sound sys reader support entry fitted valid p satisfied entryBudget entryDecreasing
  simpa only [phaseExact,heroExact,←same] using result
end NetHack.Soko12Forward220.Unified
