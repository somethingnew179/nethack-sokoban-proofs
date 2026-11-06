/- Full original Trace reduction: only gamma in phases0..5 needs local
certificates. All other original phases and all Model actions are retained.
No unconditional220 lower bound until LocalEarly is proved. -/
import NetHack.Soko12Forward220.Candidate
import NetHack.Soko12Forward219.Reduction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Reduction
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.HazardPhaseCountedCorrection

abbrev prior := NetHack.Sokoban12CostPartition.certificate
abbrev phases := NetHack.SokobanLinearPhases.Map12.certificate

def LocalEarly : Prop := ∀ phase, phase < 6 →
  ∀ hero ∈ NetHack.SokobanLinearPhases.Map12.heroes phase,
  ∀ direction p outcome,
  stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates phase) p)
    (project (soko1_2.initial.holes.drop phase)) hero direction = some outcome →
  ((NetHack.SokobanLinearPhases.Map12.crates phase).filter p).length ≤ 20-phase →
  DecisionDAG.eval Shared.read (afterBoxes p outcome) (Shared.gamma (nextPhase phase outcome) (nextHero outcome)) <
    DecisionDAG.eval Shared.read p (Shared.gamma phase hero) →
  prior.bonus hero p + DecisionDAG.eval Shared.read p (Shared.gamma phase hero) ≤
    slack Generated.soko1_2Potential outcome + prior.bonus (nextHero outcome) (afterBoxes p outcome) +
      DecisionDAG.eval Shared.read (afterBoxes p outcome) (Shared.gamma (nextPhase phase outcome) (nextHero outcome))

noncomputable def certificate (localEarly : LocalEarly) :
    HazardPhaseCountedCorrection.Certificate soko1_2.board soko1_2.initial.holes
      Generated.soko1_2Potential prior phases where
  bonus := fun phase hero p => DecisionDAG.eval Shared.read p (Shared.gamma phase hero)
  nonnegative := fun _ _ _ => Shared.eval_nonnegative _ _
  cratesUnique := by
    intro phase
    change (NetHack.SokobanLinearPhases.Map12.crates phase).Nodup
    unfold NetHack.SokobanLinearPhases.Map12.crates
    split <;> decide +kernel
  localBound := by
    intro phase active hero member direction p outcome checked budget decreasing
    by_cases early : phase < 6
    · have normalized : ((NetHack.SokobanLinearPhases.Map12.crates phase).filter p).length ≤ 20-phase := by
        have holesCount : soko1_2.initial.holes.length = 18 := by decide +kernel
        have allowanceCount : prior.allowance = 2 := rfl
        have cratesFunction : phases.crates = NetHack.SokobanLinearPhases.Map12.crates := rfl
        have original := budget
        rw [List.length_drop, holesCount, allowanceCount, cratesFunction] at original
        omega
      exact localEarly phase early hero member direction p outcome checked normalized decreasing
    · have root := Shared.gamma_after_phase5 phase hero (by omega)
      have literal : DecisionDAG.eval Shared.read p 0 = 0 := DecisionDAG.eval_literal (by decide +kernel) _
      have nonnegative := Shared.eval_nonnegative (afterBoxes p outcome)
        (Shared.gamma (nextPhase phase outcome) (nextHero outcome))
      simp only [root, literal] at decreasing
      omega
  goal := by
    intro hero member p budget
    change ((NetHack.SokobanLinearPhases.Map12.crates 18).filter p).length ≤ prior.allowance at budget
    change prior.bonus hero p + DecisionDAG.eval Shared.read p (Shared.gamma 18 hero) ≤
      weightSum (fun c => -Generated.soko1_2Potential.boulder c)
        ((NetHack.SokobanLinearPhases.Map12.crates 18).filter p)
    have zero : DecisionDAG.eval Shared.read p (Shared.gamma 18 hero) = 0 := by
      rw [Shared.gamma_after_phase5 18 hero (by decide)]
      exact DecisionDAG.eval_literal (by decide +kernel) _
    simpa only [zero, Int.add_zero] using
      NetHack.Soko12Forward219.Reduction.terminal_old hero p budget

theorem certificate_value_eq (localEarly : LocalEarly) (s : State) :
    HazardPhaseCountedCorrection.value (certificate localEarly) s = Candidate.value s := rfl

/-- All original initial traces and costs. Six local phase obligations remain
explicit; no new Trace restriction or game rule is assumed. -/
theorem lower_bound_if_early (localEarly : LocalEarly)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves)
    (completed : Goal final) : 220 ≤ pushes := by
  apply pushes_minimal_of_potential
    (HazardPhaseCountedCorrection.stepBound (certificate localEarly) Generated.soko1_2_potential_valid)
    (HazardPhaseCountedCorrection.goalBound (certificate localEarly) Generated.soko1_2_potential_valid) 220 _ trace completed
  rw [certificate_value_eq]
  exact Candidate.initial_value

end NetHack.Soko12Forward220.Reduction
