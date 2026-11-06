/- Positive nonlinear group rows suffice: zero entries inherit the already
proved scalar certificate. Charges still belong to exactly one actual group.
This lets a finite certificate enumerate only positive pair entries without
assuming that omitted boulders vanish or restricting the original Trace. -/
import NetHack.Sokoban.GhostScalar

namespace NetHack.Sokoban.GhostNonlinear
open HazardPattern GhostPartition LowerBounds
open HazardPhaseCountedCorrection (nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def corrected {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases)
    (bonus : Nat → Cell → List Cell → Nat) (phase hero : Nat) (group : List Cell) : Int :=
  weightSum (scalar.weight phase hero) group + Int.ofNat (bonus phase hero group)

structure Correction {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases) (limit : Nat) where
  bonus : Nat → Cell → List Cell → Nat
  positive_row : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group.length ≤ limit →
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ∉ group →
    0 < bonus phase hero group → ∀ direction outcome,
    stepOracle board (PatternCorrection.project group)
      (PatternCorrection.project (original.drop phase)) hero direction = some outcome →
    corrected scalar bonus phase hero group ≤ charge scalar.holeWeight group outcome +
      corrected scalar bonus (nextPhase phase outcome) (nextHero outcome) (update group outcome)
  positive_environment : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group ⊆ phases.crates (phase+1) →
    group.length ≤ limit → hero ∈ board.floor → hero ∉ board.doors →
    hero ∉ original.drop phase → hero ∉ group → 0 < bonus phase hero group →
    corrected scalar bonus phase hero group ≤ corrected scalar bonus (phase+1) hero group
  terminal_bonus : ∀ hero group, bonus original.length hero group = 0

def asOracleCertificate {board original phases limit}
    {scalar : HeroPhasePotential.Certificate board original phases}
    (cert : Correction scalar limit) : GhostPhaseCertificate.Certificate board original phases limit where
  valueAt := corrected scalar cert.bonus
  holeWeight := scalar.holeWeight
  crate_disjoint := scalar.crate_disjoint
  row := by
    intro phase active hero heroInside group unique inside length floor door hole clear direction outcome oracle
    by_cases zero : cert.bonus phase hero group = 0
    · have baseline := (GhostScalar.asOracleCertificate scalar limit).row phase active hero heroInside
        group unique inside length floor door hole clear direction outcome oracle
      have nonnegative : 0 ≤ Int.ofNat (cert.bonus (nextPhase phase outcome) (nextHero outcome) (update group outcome)) := by
        simp only [Int.ofNat_eq_natCast]; omega
      change weightSum (scalar.weight phase hero) group ≤ charge scalar.holeWeight group outcome +
        weightSum (scalar.weight (nextPhase phase outcome) (nextHero outcome)) (update group outcome) at baseline
      unfold corrected
      rw [zero]
      simp only [Int.ofNat_eq_natCast] at *
      omega
    · exact cert.positive_row phase active hero heroInside group unique inside length floor door hole clear
        (by omega) direction outcome oracle
  environment := by
    intro phase active hero heroInside group unique inside nextInside length floor door hole clear
    by_cases zero : cert.bonus phase hero group = 0
    · have baseline := (GhostScalar.asOracleCertificate scalar limit).environment phase active hero heroInside
        group unique inside nextInside length floor door hole clear
      have nonnegative : 0 ≤ Int.ofNat (cert.bonus (phase+1) hero group) := by
        simp only [Int.ofNat_eq_natCast]; omega
      change weightSum (scalar.weight phase hero) group ≤ weightSum (scalar.weight (phase+1) hero) group at baseline
      unfold corrected
      rw [zero]
      simp only [Int.ofNat_eq_natCast] at *
      omega
    · exact cert.positive_environment phase active hero heroInside group unique inside nextInside length
        floor door hole clear (by omega)
  terminal := by
    intro hero group unique length
    have bound := weightSum_nonpositive (scalar.weight original.length hero) group (scalar.terminal hero)
    unfold corrected
    rw [cert.terminal_bonus]
    simpa [Int.ofNat_eq_natCast] using bound

def asOriginalCertificate {board original phases limit}
    {scalar : HeroPhasePotential.Certificate board original phases} (cert : Correction scalar limit) :
    GroupCertificate board limit (HazardPhases.Good phases) :=
  GhostPhaseCertificate.asOriginalCertificate (asOracleCertificate cert)

end NetHack.Sokoban.GhostNonlinear
