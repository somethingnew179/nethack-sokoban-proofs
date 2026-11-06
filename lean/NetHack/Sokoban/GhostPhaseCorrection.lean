/- Positive corrections of any proved group oracle certificate. Zero
entries inherit the entire proved base, including last-fill mass bounds. Charges still belong to exactly one actual group.
This lets a finite certificate enumerate only positive pair entries without
assuming that omitted boulders vanish or restricting the original Trace. -/
import NetHack.Sokoban.GhostPhaseCertificate

namespace NetHack.Sokoban.GhostPhaseCorrection
open HazardPattern GhostPartition LowerBounds
open HazardPhaseCountedCorrection (nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def corrected {board original phases limit}
    (basis : GhostPhaseCertificate.Certificate board original phases limit)
    (bonus : Nat → Cell → List Cell → Nat) (phase hero : Nat) (group : List Cell) : Int :=
  basis.valueAt phase hero group + Int.ofNat (bonus phase hero group)

structure Correction {board original phases limit}
    (basis : GhostPhaseCertificate.Certificate board original phases limit) where
  bonus : Nat → Cell → List Cell → Nat
  positive_row : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group.length ≤ limit →
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ∉ group →
    0 < bonus phase hero group → ∀ direction outcome,
    stepOracle board (PatternCorrection.project group)
      (PatternCorrection.project (original.drop phase)) hero direction = some outcome →
    corrected basis bonus phase hero group ≤ charge basis.holeWeight group outcome +
      corrected basis bonus (nextPhase phase outcome) (nextHero outcome) (update group outcome)
  positive_environment : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group ⊆ phases.crates (phase+1) →
    group.length ≤ limit → hero ∈ board.floor → hero ∉ board.doors →
    hero ∉ original.drop phase → hero ∉ group → 0 < bonus phase hero group →
    corrected basis bonus phase hero group ≤ corrected basis bonus (phase+1) hero group
  terminal_bonus : ∀ hero group, bonus original.length hero group = 0

def asOracleCertificate {board original phases limit}
    {basis : GhostPhaseCertificate.Certificate board original phases limit}
    (cert : Correction basis) : GhostPhaseCertificate.Certificate board original phases limit where
  valueAt := corrected basis cert.bonus
  holeWeight := basis.holeWeight
  crate_disjoint := basis.crate_disjoint
  row := by
    intro phase active hero heroInside group unique inside length floor door hole clear direction outcome oracle
    by_cases zero : cert.bonus phase hero group = 0
    · have baseline := basis.row phase active hero heroInside
        group unique inside length floor door hole clear direction outcome oracle
      have nonnegative : 0 ≤ Int.ofNat (cert.bonus (nextPhase phase outcome) (nextHero outcome) (update group outcome)) := by
        simp only [Int.ofNat_eq_natCast]; omega
      change basis.valueAt phase hero group ≤ charge basis.holeWeight group outcome +
        basis.valueAt (nextPhase phase outcome) (nextHero outcome) (update group outcome) at baseline
      unfold corrected
      rw [zero]
      simp only [Int.ofNat_eq_natCast] at *
      omega
    · exact cert.positive_row phase active hero heroInside group unique inside length floor door hole clear
        (by omega) direction outcome oracle
  environment := by
    intro phase active hero heroInside group unique inside nextInside length floor door hole clear
    by_cases zero : cert.bonus phase hero group = 0
    · have baseline := basis.environment phase active hero heroInside
        group unique inside nextInside length floor door hole clear
      have nonnegative : 0 ≤ Int.ofNat (cert.bonus (phase+1) hero group) := by
        simp only [Int.ofNat_eq_natCast]; omega
      change basis.valueAt phase hero group ≤ basis.valueAt (phase+1) hero group at baseline
      unfold corrected
      rw [zero]
      simp only [Int.ofNat_eq_natCast] at *
      omega
    · exact cert.positive_environment phase active hero heroInside group unique inside nextInside length
        floor door hole clear (by omega)
  terminal := by
    intro hero group unique length
    have bound := basis.terminal hero group unique length
    unfold corrected
    rw [cert.terminal_bonus]
    simpa [Int.ofNat_eq_natCast] using bound

def asOriginalCertificate {board original phases limit}
    {basis : GhostPhaseCertificate.Certificate board original phases limit} (cert : Correction basis) :
    GroupCertificate board limit (HazardPhases.Good phases) :=
  GhostPhaseCertificate.asOriginalCertificate (asOracleCertificate cert)

end NetHack.Sokoban.GhostPhaseCorrection
