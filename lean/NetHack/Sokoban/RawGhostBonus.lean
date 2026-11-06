/- A raw nonlinear credit spends slack only on its OWN persistent boulders.
An outside push is a shadow walk and spends zero credit. This theorem does
not authorize adding overlapping certificates without a disjointness proof. -/
import NetHack.Sokoban.RawPatternBonus
import NetHack.Sokoban.GhostOracleFacts
namespace NetHack.Sokoban.RawGhostBonus
open PatternCorrection LowerBounds HazardPattern GhostPartition GhostProjection

theorem update_projected (group : List Cell) (outcome : Outcome) :
    update group (projectedOutcome group outcome) = update group outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result =>
    by_cases owner : source ∈ group <;> simp only [projectedOutcome,update,move,owner,↓reduceIte]

theorem hero_projected (group : List Cell) (outcome : Outcome) :
    nextHero (projectedOutcome group outcome) = nextHero outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result =>
    by_cases owner : source ∈ group <;> simp only [projectedOutcome,owner,↓reduceIte,nextHero]

theorem step_charge {board original potential} (cert : Certificate board original potential)
    (state : State) (unique : state.boulders.Nodup) (holesSubset : state.holes ⊆ original)
    (disjoint : ∀ box ∈ state.boulders, box ∉ state.holes)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    (dir : Dir) (t : Transition) (checked : step board state dir = some t)
    (outcome : Outcome) (effect : Matches state t outcome) :
    cert.bonus state.player (project group) ≤
      slack potential (projectedOutcome group outcome) +
        cert.bonus t.state.player (project (update group outcome)) := by
  let shadow : State := ⟨state.player,group,state.holes⟩
  have physical := step_player_clear board state dir t checked
  have clear : state.player ∉ group := fun h => physical.2.2.1 (subset h)
  have standing : standingAllowed board shadow = true := by
    simp [standingAllowed,shadow,physical.1,physical.2.1,clear,physical.2.2.2]
  have active : goal shadow = false := by
    have core : exposedStep board state dir = some t := (exposedStep_eq board state dir).trans checked
    cases ongoing : goal state with
    | false => exact ongoing
    | true => simp [exposedStep,ongoing] at core
  have oracle := original_matches_shadow board state group unique subset disjoint dir t checked outcome effect
  obtain ⟨u,shadowStep,shadowEffect⟩ := oracle_realized board shadow groupUnique standing active dir
    (projectedOutcome group outcome) oracle
  have bound := RawPatternBonus.raw_step cert shadow groupUnique holesSubset dir u shadowStep
  have delta := matches_delta potential shadow u (projectedOutcome group outcome) shadowEffect
  have boxes : u.state.boulders = update group outcome := by
    have h := GhostOracleFacts.matches_update shadow u _ shadowEffect
    change u.state.boulders = update group (projectedOutcome group outcome) at h
    exact h.trans (update_projected group outcome)
  have hero : u.state.player = t.state.player :=
    (HazardPattern.matches_hero shadow u _ shadowEffect).trans
      ((hero_projected group outcome).trans
        (HazardPattern.matches_hero state t outcome effect).symm)
  rw [boxes,hero] at bound
  change potential.value shadow + cert.bonus state.player (project group) ≤
    Int.ofNat u.pushCost + potential.value u.state + cert.bonus t.state.player (project (update group outcome)) at bound
  omega

end NetHack.Sokoban.RawGhostBonus
