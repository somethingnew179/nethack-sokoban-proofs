import Owner1007.OwnedStrict11
import Owner1007.LeftActor11

namespace Owner1007.LeftStrict11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

theorem outcome_stay {state : State} {t : Transition} {outcome : Outcome} {source landing : Cell}
    (effect : Matches state t outcome) (sourceEq : t.pushSource = some source)
    (landingEq : t.landing = some landing) (filled : t.filled = none) :
    outcome = .push source (.stay landing) := by
  cases outcome with
  | walk target =>
    rw [effect] at sourceEq
    cases sourceEq
  | push other ending =>
    cases ending with
    | stay there =>
      have same : other = source := by simpa only [effect.2, Option.some.injEq] using sourceEq
      have landed : there = landing := by simpa only [effect.2, Option.some.injEq] using landingEq
      subst other; subst there
      rfl
    | fill hole =>
      simp only [effect.2.2] at filled
      contradiction

theorem exit_row {phases : HazardPhases.Certificate soko1_1.board soko1_1.initial.holes}
    (scalar : HeroPhasePotential.Certificate soko1_1.board soko1_1.initial.holes phases)
    (weightEq : scalar.weight = NetHack.Soko11Hero315.weight)
    {state : State} {direction : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
    (good : HazardPhases.Good phases state) (checked : step soko1_1.board state direction = some t)
    (effect : Matches state t outcome) (unique : group.Nodup) (inside : group ⊆ state.boulders)
    (pays : ∃ source, source ∈ group ∧ t.pushSource = some source ∧ LeftActor11.Exit source direction) :
    2 ≤ charge scalar.holeWeight group outcome +
      OwnedStrict11.groupValue scalar t.state (update group outcome) -
      OwnedStrict11.groupValue scalar state group := by
  obtain ⟨source,owner,sourceEq,exit⟩ := pays
  obtain ⟨phase,atIndex⟩ := good.2
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
  have within : HazardPhases.At phases (phaseOf soko1_1.initial.holes state) state := by
    rw [←phaseEq]; exact atIndex
  have active := HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
  have holesInside : state.holes ⊆ soko1_1.initial.holes := by
    rw [atIndex.2.1]
    exact (List.drop_sublist phase soko1_1.initial.holes).subset
  have active16 : phaseOf soko1_1.initial.holes state < 16 := active
  obtain ⟨landing,landed,unfilled,price⟩ := LeftActor11.exit_price checked sourceEq exit holesInside
    (phaseOf soko1_1.initial.holes state) active16
  have same := outcome_stay effect sourceEq landed unfilled
  subst outcome
  have ownPrice : 2 ≤ 1 + scalar.weight (phaseOf soko1_1.initial.holes state) source landing -
      scalar.weight (phaseOf soko1_1.initial.holes state) state.player source := by
    rw [weightEq]
    change 2 ≤ ActorPrices11.price _ _ _ _
    omega
  exact OwnedStrict11.owned_stay_bound scalar state direction t good checked source landing effect
    group unique inside owner 2 ownPrice
#print axioms exit_row
end Owner1007.LeftStrict11
