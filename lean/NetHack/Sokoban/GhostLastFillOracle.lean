/- Oracle form of the fully proved one-remaining-hazard group bound.
It can be used as a base for sparse excess rows of a larger pair table. -/
import NetHack.Sokoban.GhostLastFill
import NetHack.Sokoban.GhostOracleLift
namespace NetHack.Sokoban.GhostLastFillOracle
open GhostPartition LowerBounds HazardPattern
open HazardPhaseCountedCorrection (phaseOf)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def valueAt {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (phase hero : Nat) (group : List Cell) : Int :=
  if original.length = phase+1 then
    match group with
    | [a,b] => min (scalar.weight phase hero a) (scalar.weight phase hero b)
    | _ => weightSum (scalar.weight phase hero) group
  else weightSum (scalar.weight phase hero) group

theorem represents {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (state : State) (group : List Cell) :
    GhostLastFill.value scalar state group = valueAt scalar (phaseOf original state) state.player group := rfl

private def atPhase (original : List Cell) (phase hero : Nat) : State := ⟨hero,[],original.drop phase⟩
private theorem atPhase_index (original : List Cell) (phase hero : Nat) (bound : phase ≤ original.length) :
    phaseOf original (atPhase original phase hero) = phase := by
  simp only [phaseOf,atPhase,List.length_drop]
  omega

theorem dominates {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (nonpositive : ∀ phase hero box, scalar.weight phase hero box ≤ 0)
    (phase hero : Nat) (group : List Cell) (bound : phase ≤ original.length) :
    weightSum (scalar.weight phase hero) group ≤ valueAt scalar phase hero group := by
  have d := GhostLastFill.dominates scalar nonpositive (atPhase original phase hero) group
  change weightSum (scalar.weight (phaseOf original (atPhase original phase hero)) hero) group ≤
    valueAt scalar (phaseOf original (atPhase original phase hero)) hero group at d
  rw [atPhase_index original phase hero bound] at d
  exact d

theorem nonpositive {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (weights : ∀ phase hero box, scalar.weight phase hero box ≤ 0)
    (phase hero : Nat) (group : List Cell) : valueAt scalar phase hero group ≤ 0 := by
  have sum := weightSum_nonpositive (scalar.weight phase hero) group (weights phase hero)
  unfold valueAt
  split
  · cases group with
    | nil => exact sum
    | cons a rest =>
      cases rest with
      | nil => exact sum
      | cons b tail =>
        cases tail with
        | nil => exact Int.le_trans (Int.min_le_left _ _) (weights phase hero a)
        | cons c rest => exact sum
  · exact sum

theorem terminal_zero {board original phases} (scalar : HeroPhasePotential.Certificate board original phases)
    (zero : ∀ hero box, scalar.weight original.length hero box = 0) (hero : Nat) (group : List Cell) :
    valueAt scalar original.length hero group = 0 := by
  have notLast : ¬ original.length = original.length+1 := by omega
  unfold valueAt
  rw [if_neg notLast]
  induction group with
  | nil => rfl
  | cons first rest ih => rw [weightSum_cons,zero,ih]; rfl

def asOracleCertificate {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases)
    (weights : ∀ phase hero box, scalar.weight phase hero box ≤ 0)
    (zero : ∀ hero box, scalar.weight original.length hero box = 0) :
    GhostPhaseCertificate.Certificate board original phases 2 :=
  GhostOracleLift.ofOriginal (GhostLastFill.asOriginalCertificate scalar weights zero) (valueAt scalar)
    (represents scalar) scalar.crate_disjoint (by
      intro phase active hero heroInside group unique inside nextInside length floor door hole clear
      by_cases last : original.length = phase+1
      · have before := nonpositive scalar weights phase hero group
        have after := terminal_zero scalar zero hero group
        rw [←last]
        rw [after]
        exact before
      · have baseline := (GhostScalar.asOracleCertificate scalar 2).environment phase active hero heroInside
          group unique inside nextInside length floor door hole clear
        have after := dominates scalar weights (phase+1) hero group (by omega)
        change valueAt scalar phase hero group ≤ valueAt scalar (phase+1) hero group
        have beforeEq : valueAt scalar phase hero group = weightSum (scalar.weight phase hero) group := by
          simp only [valueAt,if_neg last]
        rw [beforeEq]
        exact Int.le_trans baseline after)
    (fun hero group _ _ => by rw [terminal_zero scalar zero]; exact Int.le_refl 0)

end NetHack.Sokoban.GhostLastFillOracle
