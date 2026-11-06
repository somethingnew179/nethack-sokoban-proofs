/- Transfer of ALL interior action/environment obligations to phase14,
including exact RLT endpoint normalization, consumption and hole charges.
This is a conditional reduction until phase14 rows are supplied. -/
import NetHack.Soko11PairCandidate321.InteriorGeometry
import NetHack.Soko11PairCandidate321.PhaseFields
import NetHack.Sokoban.GhostOracleFacts
namespace NetHack.Soko11PairCandidate321
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostHoleTransfer
open NetHack.Sokoban.HazardPhaseCountedCorrection (nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def endpointWeightCheck : Bool :=
  (NetHack.Soko11Hero315.phases.heroes 14).all fun hero =>
    (NetHack.Soko11Hero315.phases.crates 14).all fun box =>
      decide (NetHack.Soko11Hero315.weight 14 hero box = NetHack.Soko11Hero315.weight 15 hero box)
theorem endpoint_weights_checked : endpointWeightCheck = true := by decide +kernel
theorem endpoint_weight (hero box : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes 14)
    (boxInside : box ∈ NetHack.Soko11Hero315.phases.crates 14) :
    NetHack.Soko11Hero315.weight 14 hero box = NetHack.Soko11Hero315.weight 15 hero box :=
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp endpoint_weights_checked hero heroInside) box boxInside)

def heroGrowthCheck : Bool := (List.range 16).all fun phase =>
  decide (NetHack.Soko11Hero315.phases.heroes phase ⊆ NetHack.Soko11Hero315.phases.heroes (phase+1))
theorem hero_growth_checked : heroGrowthCheck = true := by decide +kernel
theorem hero_growth (phase : Nat) (active : phase < 16) :
    NetHack.Soko11Hero315.phases.heroes phase ⊆ NetHack.Soko11Hero315.phases.heroes (phase+1) :=
  of_decide_eq_true (List.all_eq_true.mp hero_growth_checked phase (List.mem_range.mpr active))

def holePricesCheck : Bool := (List.range 16).all fun phase =>
  if 1 ≤ phase then (soko1_1.initial.holes.drop phase).all fun hole =>
    decide (NetHack.Soko11Hero315.holeWeight hole = 34) else true
theorem hole_prices_checked : holePricesCheck = true := by decide +kernel
theorem interior_hole_price (phase hole : Nat) (lower : 1 ≤ phase) (active : phase < 16)
    (member : hole ∈ soko1_1.initial.holes.drop phase) : NetHack.Soko11Hero315.holeWeight hole = 34 := by
  have all := List.all_eq_true.mp hole_prices_checked phase (List.mem_range.mpr active)
  simp only [if_pos lower] at all
  exact of_decide_eq_true (List.all_eq_true.mp all hole member)
theorem canonical_hole_price : NetHack.Soko11Hero315.holeWeight 48 = 34 := by decide +kernel

theorem bonus_small (phase hero : Nat) (group : List Cell) (small : group.length ≤ 1) :
    bonus phase hero group = 0 := by
  have two : ¬group.length = 2 := by omega
  simp only [bonus,if_neg two]

theorem fill_successor_value (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14)
    (hero : Cell) (heroInside : hero ∈ NetHack.Soko11Hero315.phases.heroes (phase+1))
    (group : List Cell) (inside : group ⊆ NetHack.Soko11Hero315.phases.crates (phase+1))
    (small : group.length ≤ 1) : valueAt (phase+1) hero group = valueAt 15 hero group := by
  by_cases last : phase = 14
  · subst phase; rfl
  · have nextUpper : phase+1 ≤ 14 := by omega
    have geometry := interior_support (phase+1) (by omega) nextUpper
    have equal := interior_value_equal (phase+1) (by omega) nextUpper hero heroInside group inside
    rw [equal]
    have weights := sum_congr_on (NetHack.Soko11Hero315.weight 14 hero)
      (NetHack.Soko11Hero315.weight 15 hero) group (fun box member =>
        endpoint_weight hero box (geometry.2.1 heroInside) (by rw [←geometry.1]; exact inside member))
    simp only [valueAt,bonus_small 14 hero group small,bonus_small 15 hero group small,weights]

theorem interior_actions_from14 (reference : PositiveActionsAt 14)
    (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14) : PositiveActionsAt phase := by
  intro hero heroInside group unique inside length floor door hole clear positive direction outcome oracle
  have geometry := interior_support phase lower upper
  have referenceInside : group ⊆ NetHack.Soko11Hero315.phases.crates 14 := by rw [←geometry.1]; exact inside
  have sameBonus := interior_bonus_equal phase lower upper hero heroInside group inside
  have positive14 : 0 < bonus 14 hero group := by rw [←sameBonus]; exact positive
  have hole14 : hero ∉ soko1_1.initial.holes.drop 14 := fun h => hole (geometry.2.2 h)
  have transfer := interior_oracle_transfer phase lower upper hero group inside hole direction outcome oracle
  have bound := reference hero (geometry.2.1 heroInside) group unique referenceInside length
    floor door hole14 clear positive14 direction (canonicalOutcome 48 outcome) transfer
  have successor := GhostOracleFacts.successor NetHack.Soko11Hero315.phases phase (by change phase < 16; omega)
    hero heroInside group unique inside floor door hole clear direction outcome oracle
  have before := interior_value_equal phase lower upper hero heroInside group inside
  cases outcome with
  | walk target =>
    have after := interior_value_equal phase lower upper target successor.1 group successor.2.1
    simpa only [localBound,canonicalOutcome,nextPhase,nextHero,update,charge,before,after] using bound
  | push source result =>
    cases result with
    | stay landing =>
      have after := interior_value_equal phase lower upper source successor.1
        (update group (.push source (.stay landing))) successor.2.1
      simpa only [localBound,canonicalOutcome,canonicalEnding,nextPhase,nextHero,before,after] using bound
    | fill filled =>
      have owner : source ∈ group := successor.2.2.1
      have price := interior_hole_price phase filled lower (by omega) successor.2.2.2
      have shorter := List.length_erase_of_mem owner
      have small : (update group (.push source (.fill filled))).length ≤ 1 := by
        simp only [update,move,if_pos owner,post]
        omega
      have after := fill_successor_value phase lower upper source successor.1
        (update group (.push source (.fill filled))) successor.2.1 small
      have sameUpdate : update group (.push source (.fill filled)) = update group (.push source (.fill 48)) := rfl
      unfold localBound at bound ⊢
      simp only [canonicalOutcome,canonicalEnding,nextPhase,nextHero] at bound ⊢
      rw [before,after,sameUpdate]
      simpa only [charge,if_pos owner,price,canonical_hole_price] using bound

theorem interior_environments_from14 (reference : PositiveEnvironmentsAt 14)
    (phase : Nat) (lower : 1 ≤ phase) (upper : phase ≤ 14) : PositiveEnvironmentsAt phase := by
  by_cases last : phase = 14
  · subst phase; exact reference
  · intro hero heroInside group unique inside nextInside length floor door hole clear positive
    have afterHero := hero_growth phase (by omega) heroInside
    rw [interior_value_equal phase lower upper hero heroInside group inside,
      interior_value_equal (phase+1) (by omega) (by omega) hero afterHero group nextInside]
    exact Int.le_refl _

end NetHack.Soko11PairCandidate321
