/- Physical successor facts for a persistent group oracle, derived by
realizing its edge in the unchanged Model and using the proved phase invariant. -/
import NetHack.Sokoban.GhostOracleLift
namespace NetHack.Sokoban.GhostOracleFacts
open HazardPattern GhostPartition
open HazardPhaseCountedCorrection (phaseOf nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem matches_update (state : State) (t : Transition) (outcome : Outcome)
    (effect : Matches state t outcome) : t.state.boulders = update state.boulders outcome := by
  cases outcome with
  | walk target => rw [effect]; rfl
  | push source result =>
    cases result with
    | stay landing =>
      rcases effect with ⟨present,rfl⟩
      simp only [update,move,if_pos present,post]
    | fill hole =>
      rcases effect with ⟨present,member,rfl⟩
      simp only [update,move,if_pos present,post]

theorem successor {board original} (phases : HazardPhases.Certificate board original)
    (phase : Nat) (active : phase < original.length) (hero : Cell) (heroInside : hero ∈ phases.heroes phase)
    (group : List Cell) (unique : group.Nodup) (inside : group ⊆ phases.crates phase)
    (floor : hero ∈ board.floor) (door : hero ∉ board.doors)
    (hole : hero ∉ original.drop phase) (clear : hero ∉ group)
    (direction : Dir) (outcome : Outcome)
    (oracle : stepOracle board (PatternCorrection.project group)
      (PatternCorrection.project (original.drop phase)) hero direction = some outcome) :
    nextHero outcome ∈ phases.heroes (nextPhase phase outcome) ∧
    update group outcome ⊆ phases.crates (nextPhase phase outcome) ∧
    (match outcome with
     | .push source (.fill hole) => source ∈ group ∧ hole ∈ original.drop phase
     | .push source (.stay _) => source ∈ group
     | .walk _ => True) := by
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
  have nextGood := HazardPhases.step_good phases shadow direction t good checked
  rcases nextGood.2 with ⟨index,atNext⟩
  have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase shadow atIndex
  have canonicalAt : HazardPhases.At phases (phaseOf original shadow) shadow := by rw [←phaseEq]; exact atIndex
  have afterPhase := HazardPhaseCountedCorrection.matches_phase phases shadow t canonicalAt outcome effect
  have afterEq : index = nextPhase phase outcome := by
    have canonical := HazardPhaseCountedCorrection.at_phase phases index t.state atNext
    rw [afterPhase,←phaseEq] at canonical
    exact canonical
  rw [afterEq] at atNext
  have afterHero := matches_hero shadow t outcome effect
  have afterGroup := matches_update shadow t outcome effect
  refine ⟨?_,?_,?_⟩
  · rw [←afterHero]; exact atNext.2.2.1
  · rw [←afterGroup]; exact atNext.2.2.2
  · cases outcome with
    | walk _ => trivial
    | push source result =>
      cases result with
      | stay _ => exact effect.1
      | fill _ => exact ⟨effect.1,effect.2.1⟩

end NetHack.Sokoban.GhostOracleFacts
