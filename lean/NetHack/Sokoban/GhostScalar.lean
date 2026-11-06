/- The existing certified scalar is an additive persistent-group base.
Its group rows hold for arbitrary distinct selected boulders, not merely the
positive entries of a proposed pair table. This covers missing/zero bonuses. -/
import NetHack.Sokoban.GhostPhaseCertificate
import NetHack.Sokoban.OracleComplete
import NetHack.Sokoban.StatePermutation

namespace NetHack.Sokoban.GhostScalar
open HazardPattern GhostPartition LowerBounds
open HazardPhaseCountedCorrection (phaseOf nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def asOracleCertificate {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases) (limit : Nat) :
    GhostPhaseCertificate.Certificate board original phases limit where
  valueAt := fun phase hero group => weightSum (scalar.weight phase hero) group
  holeWeight := scalar.holeWeight
  crate_disjoint := scalar.crate_disjoint
  row := by
    intro phase active hero heroInside group groupUnique groupInside groupLength
      heroFloor heroDoor heroHole heroGroup direction outcome oracle
    let shadow : State := ⟨hero,group,original.drop phase⟩
    have standing : standingAllowed board shadow = true := by
      simp [standingAllowed,shadow,heroFloor,heroDoor,heroHole,heroGroup]
    have holesPositive : 0 < (original.drop phase).length := by rw [List.length_drop]; omega
    have ongoing : goal shadow = false := by
      cases holes : original.drop phase with
      | nil => simp only [holes,List.length_nil] at holesPositive; omega
      | cons first rest => simp [goal,shadow,holes]
    have atIndex : HazardPhases.At phases phase shadow :=
      ⟨by omega,rfl,heroInside,groupInside⟩
    have good : HazardPhases.Good phases shadow := ⟨groupUnique,phase,atIndex⟩
    rcases GhostProjection.oracle_realized board shadow groupUnique standing ongoing direction outcome oracle with
      ⟨t,checked,effect⟩
    have bound := HeroPhasePotential.step_bound scalar shadow direction t good checked
    have beforePhase := HazardPhaseCountedCorrection.at_phase phases phase shadow atIndex
    have canonicalAt : HazardPhases.At phases (phaseOf original shadow) shadow := by
      rw [←beforePhase]
      exact atIndex
    have afterPhase := HazardPhaseCountedCorrection.matches_phase phases shadow t canonicalAt outcome effect
    unfold HeroPhasePotential.value at bound
    rw [afterPhase,←beforePhase] at bound
    cases outcome with
    | walk target =>
      rw [effect] at bound
      simp only [HeroPhasePotential.valueAt,nextPhase,Transition.pushCost,Bool.false_eq_true,
        ↓reduceIte,Int.ofNat_eq_natCast] at bound
      change weightSum (scalar.weight phase hero) group ≤
        charge scalar.holeWeight group (.walk target) +
          weightSum (scalar.weight (nextPhase phase (.walk target)) (nextHero (.walk target)))
            (update group (.walk target))
      simp only [charge,nextPhase,nextHero,update,Int.zero_add]
      dsimp only [shadow] at bound
      omega
    | push source result =>
      have owner : source ∈ group := by cases result <;> exact effect.1
      cases result with
      | stay landing =>
        rw [effect.2] at bound
        simp only [HeroPhasePotential.valueAt,nextPhase,Transition.pushCost,↓reduceIte,
          Int.ofNat_eq_natCast] at bound
        change weightSum (scalar.weight phase hero) group ≤
          charge scalar.holeWeight group (.push source (.stay landing)) +
            weightSum (scalar.weight phase source) (update group (.push source (.stay landing)))
        simp only [charge,if_pos owner,update,move,if_pos owner,post]
        dsimp only [shadow] at bound
        omega
      | fill hole =>
        have oldHoles := weightSum_erase scalar.holeWeight shadow.holes hole effect.2.1
        rw [effect.2.2] at bound
        simp only [HeroPhasePotential.valueAt,nextPhase,Transition.pushCost,↓reduceIte,
          Int.ofNat_eq_natCast] at bound
        change weightSum (scalar.weight phase hero) group ≤
          charge scalar.holeWeight group (.push source (.fill hole)) +
            weightSum (scalar.weight (phase+1) source) (update group (.push source (.fill hole)))
        simp only [charge,if_pos owner,update,move,if_pos owner,post]
        dsimp only [shadow] at bound oldHoles
        omega
  environment := by
    intro phase active hero heroInside group groupUnique groupInside nextInside groupLength
      heroFloor heroDoor heroHole heroGroup
    exact HeroPhasePotential.weightSum_mono group _ _ (fun box member =>
      scalar.advancePhase phase active hero heroFloor heroDoor heroHole box (groupInside member)
        (nextInside member) (by intro same; apply heroGroup; simpa only [same] using member))
  terminal := by
    intro hero group groupUnique groupLength
    exact weightSum_nonpositive _ group (scalar.terminal hero)

theorem weightSum_append (weight : Cell → Int) (left right : List Cell) :
    weightSum weight (left ++ right) = weightSum weight left + weightSum weight right := by
  induction left with
  | nil => simp [weightSum]
  | cons first rest ih => simp only [List.cons_append,weightSum_cons,ih]; omega

theorem sumGroups_weightSum (weight : Cell → Int) (groups : List (List Cell)) :
    sumGroups (weightSum weight) groups = weightSum weight groups.flatten := by
  induction groups with
  | nil => rfl
  | cons first rest ih => simp only [sumGroups,List.flatten_cons,weightSum_append,ih]

/-- Grouping alone changes no scalar value. A stronger initial number needs
separately proved nonlinear pair rows, rather than double-counted push costs. -/
theorem baseline_value_eq {board original phases}
    (scalar : HeroPhasePotential.Certificate board original phases) (limit : Nat)
    (state : State) (groups : List (List Cell)) (coupled : Coupled state groups) :
    partitionValue (GhostPhaseCertificate.asOriginalCertificate (asOracleCertificate scalar limit)) state groups =
      HeroPhasePotential.value scalar state := by
  change sumGroups (weightSum (scalar.weight (phaseOf original state) state.player)) groups +
    weightSum scalar.holeWeight state.holes = HeroPhasePotential.value scalar state
  rw [sumGroups_weightSum,StatePermutation.weightSum_permutation _ coupled]
  rfl

end NetHack.Sokoban.GhostScalar
