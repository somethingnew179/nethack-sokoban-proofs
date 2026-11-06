/- Full original-map Trace reduction. Only phase0 has a nonzero candidate
bonus. Other phases are retained and discharged by nonnegativity, not removed.
LocalPhase0 remains an explicit unproved premise until all certificates and
physical bridges pass. This module does NOT claim unconditional lower219. -/
import NetHack.Soko12Forward219.Candidate

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward219.Reduction
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.HazardPhaseCountedCorrection

abbrev prior := NetHack.Sokoban12CostPartition.certificate
abbrev phases := NetHack.SokobanLinearPhases.Map12.certificate

def LocalPhase0 : Prop := ∀ hero ∈ NetHack.SokobanLinearPhases.Map12.heroes 0,
  ∀ direction p outcome,
  stepOracle soko1_2.board (boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p)
    (project (soko1_2.initial.holes.drop 0)) hero direction = some outcome →
  ((NetHack.SokobanLinearPhases.Map12.crates 0).filter p).length ≤ 20 →
  DecisionDAG.eval Shared.read (afterBoxes p outcome) (Shared.gamma (nextPhase 0 outcome) (nextHero outcome)) <
    DecisionDAG.eval Shared.read p (Shared.gamma 0 hero) →
  prior.bonus hero p + DecisionDAG.eval Shared.read p (Shared.gamma 0 hero) ≤
    slack Generated.soko1_2Potential outcome + prior.bonus (nextHero outcome) (afterBoxes p outcome) +
      DecisionDAG.eval Shared.read (afterBoxes p outcome) (Shared.gamma (nextPhase 0 outcome) (nextHero outcome))

theorem sum_sublist_le (f : Cell → Int) {small large : List Cell}
    (sub : small.Sublist large) (nonnegative : ∀ c ∈ large, 0 ≤ f c) :
    weightSum f small ≤ weightSum f large := by
  revert nonnegative
  induction sub with
  | slnil => intro _; exact Int.le_refl _
  | cons c sub ih =>
    intro nonnegative
    have tail := ih (fun a member => nonnegative a (List.mem_cons.mpr (Or.inr member)))
    have head := nonnegative c (List.mem_cons.mpr (Or.inl rfl))
    simp only [weightSum]
    omega
  | cons_cons c sub ih =>
    intro nonnegative
    have tail := ih (fun a member => nonnegative a (List.mem_cons.mpr (Or.inr member)))
    simp only [weightSum]
    omega

theorem terminal_old (hero : Cell) (p : Pattern)
    (budget : ((NetHack.SokobanLinearPhases.Map12.crates 18).filter p).length ≤ prior.allowance) :
    prior.bonus hero p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c)
      ((NetHack.SokobanLinearPhases.Map12.crates 18).filter p) := by
  have sub : prior.support.Sublist (NetHack.SokobanLinearPhases.Map12.crates 18) := by decide +kernel
  have filtered := sub.filter p
  have initial := prior.goal hero p (Nat.le_trans filtered.length_le budget)
  have nonnegative : ∀ c ∈ NetHack.SokobanLinearPhases.Map12.crates 18,
      0 ≤ -Generated.soko1_2Potential.boulder c := by decide +kernel
  have larger := sum_sublist_le (fun c => -Generated.soko1_2Potential.boulder c) filtered
    (fun c member => nonnegative c (List.mem_filter.mp member).1)
  exact Int.le_trans initial larger

noncomputable def certificate (local0 : LocalPhase0) :
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
    by_cases zero : phase = 0
    · subst phase
      change ((NetHack.SokobanLinearPhases.Map12.crates 0).filter p).length ≤ 20 at budget
      exact local0 hero member direction p outcome checked budget decreasing
    · have root : Shared.gamma phase hero = 0 := by simp only [Shared.gamma, if_neg zero]
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
      change DecisionDAG.eval Shared.read p 0 = 0
      exact DecisionDAG.eval_literal (by decide +kernel) _
    simpa only [zero, Int.add_zero] using terminal_old hero p budget

theorem certificate_value_eq (local0 : LocalPhase0) (s : State) :
    HazardPhaseCountedCorrection.value (certificate local0) s = Candidate.value s := rfl

/-- Original initial Trace/cost/goal, with the sole local phase0 premise explicit. -/
theorem lower_bound_if_phase0 (local0 : LocalPhase0)
    {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves)
    (completed : Goal final) : 219 ≤ pushes := by
  apply pushes_minimal_of_potential
    (HazardPhaseCountedCorrection.stepBound (certificate local0) Generated.soko1_2_potential_valid)
    (HazardPhaseCountedCorrection.goalBound (certificate local0) Generated.soko1_2_potential_valid) 219 _ trace completed
  rw [certificate_value_eq]
  exact Candidate.initial_value

end NetHack.Soko12Forward219.Reduction
