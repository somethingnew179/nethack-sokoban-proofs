/- Finite persistent-group oracle rows imply bounds for every ORIGINAL step.
Other boulders' consumption is a checked environment phase advance, not free
erasure of a tracked boulder. Concrete numeric row fields still need proofs. -/
import NetHack.Sokoban.GhostShadow
import NetHack.Sokoban.HeroPhasePotential.Strict

namespace NetHack.Sokoban.GhostPhaseCertificate
open HazardPattern GhostPartition
open HazardPhaseCountedCorrection (phaseOf nextPhase)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Certificate (board : Board) (original : List Cell)
    (phases : HazardPhases.Certificate board original) (limit : Nat) where
  valueAt : Nat → Cell → List Cell → Int
  holeWeight : Cell → Int
  crate_disjoint : ∀ phase, phase ≤ original.length →
    ∀ box ∈ phases.crates phase, box ∉ original.drop phase
  row : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group.length ≤ limit →
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ∉ group →
    ∀ direction outcome,
    stepOracle board (PatternCorrection.project group)
      (PatternCorrection.project (original.drop phase)) hero direction = some outcome →
    valueAt phase hero group ≤ charge holeWeight group outcome +
      valueAt (nextPhase phase outcome) (nextHero outcome) (update group outcome)
  environment : ∀ phase, phase < original.length → ∀ hero ∈ phases.heroes phase,
    ∀ group, group.Nodup → group ⊆ phases.crates phase → group ⊆ phases.crates (phase+1) → group.length ≤ limit →
    hero ∈ board.floor → hero ∉ board.doors → hero ∉ original.drop phase → hero ∉ group →
    valueAt phase hero group ≤ valueAt (phase+1) hero group
  terminal : ∀ hero group, group.Nodup → group.length ≤ limit →
    valueAt original.length hero group ≤ 0

def asOriginalCertificate {board original phases limit}
    (cert : Certificate board original phases limit) :
    GroupCertificate board limit (HazardPhases.Good phases) where
  groupValue := fun state group => cert.valueAt (phaseOf original state) state.player group
  holeWeight := cert.holeWeight
  unique := fun _ good => good.1
  preserved := HazardPhases.step_good phases
  row := by
    intro state direction t outcome group good groupUnique groupSubset groupLength checked effect
    rcases good.2 with ⟨phase,atIndex⟩
    have phaseEq := HazardPhaseCountedCorrection.at_phase phases phase state atIndex
    let index := phaseOf original state
    have within : HazardPhases.At phases index state := by
      change HazardPhases.At phases (phaseOf original state) state
      rw [←phaseEq]
      exact atIndex
    have active : index < original.length :=
      HazardPhaseCountedCorrection.active_of_step phases state within direction t checked
    have groupInside : group ⊆ phases.crates index := fun _ member => within.2.2.2 (groupSubset member)
    have disjoint : ∀ box ∈ state.boulders, box ∉ state.holes := by
      intro box member
      rw [within.2.1]
      exact cert.crate_disjoint index (by omega) box (within.2.2.2 member)
    have shadow := GhostProjection.original_matches_shadow board state group good.1 groupSubset
      disjoint direction t checked outcome effect
    rw [within.2.1] at shadow
    have standing := step_player_clear board state direction t checked
    have heroHole : state.player ∉ original.drop index := by rw [←within.2.1]; exact standing.2.2.2
    have heroGroup : state.player ∉ group := fun h => standing.2.2.1 (groupSubset h)
    have numeric := cert.row index active state.player within.2.2.1 group groupUnique groupInside
      groupLength standing.1 standing.2.1 heroHole heroGroup
      direction (GhostProjection.projectedOutcome group outcome) shadow
    have afterPhase := HazardPhaseCountedCorrection.matches_phase phases state t within outcome effect
    have afterHero := matches_hero state t outcome effect
    change cert.valueAt index state.player group ≤ charge cert.holeWeight group outcome +
      cert.valueAt (phaseOf original t.state) t.state.player (update group outcome)
    rw [afterPhase,afterHero]
    cases outcome with
    | walk target => exact numeric
    | push source result =>
      by_cases owner : source ∈ group
      · simpa only [GhostProjection.projectedOutcome,if_pos owner] using numeric
      · have before : cert.valueAt index state.player group ≤ cert.valueAt index source group := by
          simpa only [GhostProjection.projectedOutcome,if_neg owner,charge,nextPhase,nextHero,
            update,Int.zero_add] using numeric
        cases result with
        | stay landing =>
          simpa only [charge,if_neg owner,nextPhase,nextHero,update,move,if_neg owner,Int.zero_add] using before
        | fill hole =>
          have targetInfo := HeroPhasePotential.step_target board state direction t checked
          have targetHero := matches_hero state t (.push source (.fill hole)) effect
          change t.state.player = source at targetHero
          rw [targetHero] at targetInfo
          have sourceInside := within.2.2.2 effect.1
          have sourceHole := cert.crate_disjoint index (by omega) source sourceInside
          have hero := phases.walk index active state.player within.2.2.1 direction source
            targetInfo.1 targetInfo.2.1 sourceHole
          have nextGood := HazardPhases.step_good phases state direction t good checked
          rcases nextGood.2 with ⟨nextIndex,nextAt⟩
          have nextEq : nextIndex = index+1 := by
            have h := HazardPhaseCountedCorrection.at_phase phases nextIndex t.state nextAt
            exact h.trans afterPhase
          rw [nextEq] at nextAt
          have nextInside : group ⊆ phases.crates (index+1) := by
            intro box member
            apply nextAt.2.2.2
            rw [effect.2.2]
            apply good.1.mem_erase_iff.mpr
            refine ⟨?_,groupSubset member⟩
            intro same
            exact owner (same ▸ member)
          have later := cert.environment index active source hero group groupUnique groupInside nextInside groupLength
            targetInfo.2.1 targetInfo.2.2 sourceHole owner
          simpa only [charge,if_neg owner,nextPhase,nextHero,update,move,if_neg owner,Int.zero_add] using
            Int.le_trans before later
  terminal := by
    intro state group good completed groupUnique groupSubset groupLength
    have empty : state.holes = [] := completed
    have last : phaseOf original state = original.length := by
      simp only [phaseOf,empty,List.length_nil,Nat.sub_zero]
    change cert.valueAt (phaseOf original state) state.player group ≤ 0
    rw [last]
    exact cert.terminal state.player group groupUnique groupLength

end NetHack.Sokoban.GhostPhaseCertificate
