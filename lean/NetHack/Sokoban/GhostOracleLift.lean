/- A group bound already proved on real Model steps can supply the local
oracle rows of a later certificate. Oracle realization and original phase
invariants discharge the reduction; no search completeness is assumed. -/
import NetHack.Sokoban.GhostPhaseCertificate
import NetHack.Sokoban.OracleComplete
namespace NetHack.Sokoban.GhostOracleLift
open HazardPattern GhostPartition
open HazardPhaseCountedCorrection (phaseOf nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def ofOriginal {board original phases limit}
    (cert : GroupCertificate board limit (HazardPhases.Good phases))
    (valueAt : Nat → Cell → List Cell → Int)
    (represents : ∀ state group, cert.groupValue state group = valueAt (phaseOf original state) state.player group)
    (disjoint : ∀ phase, phase ≤ original.length → ∀ box ∈ phases.crates phase, box ∉ original.drop phase)
    (environment : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
      ∀ group, group.Nodup → group ⊆ phases.crates phase → group ⊆ phases.crates (phase+1) →
      group.length ≤ limit → hero ∈ board.floor → hero ∉ board.doors →
      hero ∉ original.drop phase → hero ∉ group → valueAt phase hero group ≤ valueAt (phase+1) hero group)
    (terminal : ∀ hero group, group.Nodup → group.length ≤ limit → valueAt original.length hero group ≤ 0) :
    GhostPhaseCertificate.Certificate board original phases limit where
  valueAt := valueAt
  holeWeight := cert.holeWeight
  crate_disjoint := disjoint
  environment := environment
  terminal := terminal
  row := by
    intro phase active hero heroInside group unique inside length floor door hole clear direction outcome oracle
    let shadow : State := ⟨hero,group,original.drop phase⟩
    have standing : standingAllowed board shadow = true := by simp [standingAllowed,shadow,floor,door,hole,clear]
    have positive : 0 < (original.drop phase).length := by rw [List.length_drop]; omega
    have ongoing : goal shadow = false := by
      cases holes : original.drop phase with
      | nil => simp only [holes,List.length_nil] at positive; omega
      | cons first rest => simp [goal,shadow,holes]
    have atIndex : HazardPhases.At phases phase shadow := ⟨by omega,rfl,heroInside,inside⟩
    have good : HazardPhases.Good phases shadow := ⟨unique,phase,atIndex⟩
    rcases GhostProjection.oracle_realized board shadow unique standing ongoing direction outcome oracle with
      ⟨t,checked,effect⟩
    have bound := cert.row shadow direction t outcome group good unique (fun _ h => h) length checked effect
    rw [represents,represents] at bound
    have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase shadow atIndex
    have canonicalAt : HazardPhases.At phases (phaseOf original shadow) shadow := by rw [←phaseEq]; exact atIndex
    have afterPhase := HazardPhaseCountedCorrection.matches_phase phases shadow t canonicalAt outcome effect
    rw [afterPhase,←phaseEq,matches_hero shadow t outcome effect] at bound
    exact bound

end NetHack.Sokoban.GhostOracleLift
