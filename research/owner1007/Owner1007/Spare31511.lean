import Owner1007.Tight32611
import Owner1007.LoggedEventGap11
import Owner1007.Left186Before18811
namespace Owner1007.Spare31511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prices : (List.range 16).all (fun p=>decide (ActorPrices11.price p 314 315 316=1 ∧ActorPrices11.price p 316 315 314=1))=true := by decide +kernel
theorem head_ew {state : State} {dir : Dir} {t : Transition}
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some 315) : dir=.east∨dir=.west := by
 rcases step_cases_full _ _ _ _ head with walked|pushed
 ·obtain ⟨target,_,_,_,_,shape⟩ := walked
  simp only [shape] at metadata
  contradiction
 ·obtain ⟨source,result,_,_,_,push,shape⟩ := pushed
  have same : source=315 := by simpa only [shape,Option.some.injEq] using metadata
  subst source
  have target := (pushBoulder_spec _ _ _ _ _ push).2
  have checked : allDirs.all (fun dir=>decide (pushTargets soko1_1.board 315 dir=[]∨dir=.east∨dir=.west))=true := by decide +kernel
  have choice := of_decide_eq_true (List.all_eq_true.mp checked dir (Geometry.all_directions dir))
  rcases choice with empty|east|west
  ·rw [empty] at target
   contradiction
  ·exact Or.inl east
  ·exact Or.inr west

theorem initial_row {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {group : List Cell}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
 (unique : group.Nodup) (inside : group⊆state.boulders)
 (owner : 315∈group) (metadata : t.pushSource=some 315) :
 1≤charge NetHack.Soko11Hero315.holeWeight group outcome+
   value t.state (update group outcome)-value state group := by
 obtain ⟨phase,atIndex⟩ := valid.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
     (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
 have active := HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
 have priceRow := of_decide_eq_true (List.all_eq_true.mp prices _ (List.mem_range.mpr active))
 have holesInside : state.holes⊆soko1_1.initial.holes := by rw [atIndex.2.1];exact (List.drop_sublist phase _).subset
 rcases head_ew head metadata with east|west
 ·have target : pushTargets soko1_1.board 315 dir=[316] := by rw [east];decide +kernel
  have outcomeEq := UpperHeadCases11.ordinary_effect head effect metadata target (by decide +kernel) holesInside
  subst outcome
  have hero := ActorPrices11.support_of_check 315 state.player .east 314 (by decide +kernel)
    (step_player_clear _ _ _ _ head).1 (by simpa only [east] using PairPost11.source_adjacent head metadata)
  have price : 1≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 315 316-
      scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 315 := by
   change 1≤ActorPrices11.price _ state.player 315 316
   rw [hero]
   omega
  exact OwnedStrict11.owned_stay_bound scalar state dir t valid head 315 316 effect group unique inside owner 1 price
 ·have target : pushTargets soko1_1.board 315 dir=[314] := by rw [west];decide +kernel
  have outcomeEq := UpperHeadCases11.ordinary_effect head effect metadata target (by decide +kernel) holesInside
  subst outcome
  have hero := ActorPrices11.support_of_check 315 state.player .west 316 (by decide +kernel)
    (step_player_clear _ _ _ _ head).1 (by simpa only [west] using PairPost11.source_adjacent head metadata)
  have price : 1≤1+scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) 315 314-
      scalar.weight (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state.player 315 := by
   change 1≤ActorPrices11.price _ state.player 315 314
   rw [hero]
   omega
  exact OwnedStrict11.owned_stay_bound scalar state dir t valid head 315 314 effect group unique inside owner 1 price

theorem moved_positive {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (moved : ownPushes [315] outcomes≠0) : 1≤energy soko1_1.initial final [315] outcomes := by
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 315) logged [315] with found|quiet
 ·obtain ⟨cut⟩ := found
  have fixed := cut.before.fixed (by decide :315∈([315] : List Cell)) (by intro dir;rfl)
  have tag := no_push_unchanged [315] cut.beforeOutcomes fixed
  obtain ⟨source,owner,metadata,same⟩ := cut.headPaid
  change source=315 at same
  subst source
  have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
  have selected := cut.before.logged.end_subset (by decide) [315] (by decide) (by decide)
  have owns : 315∈endGroup [315] cut.beforeOutcomes := by rw [tag];simp
  have row := initial_row valid cut.headChecked cut.headEffect selected.1 selected.2 owns metadata
  have bound := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after [315] (by decide) (by decide)
  have positive := Int.le_trans row bound
  simpa only [←cut.outcomesEq] using positive
 ·exact False.elim (moved (quiet.fixed (by decide :315∈([315] : List Cell)) (by intro dir;rfl)))

theorem survives {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) : endGroup [315] outcomes≠[] := by
 obtain ⟨_,_,_,rest⟩ := Tight32611.budgets logged completed cheap
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 have nn := energy_nonnegative logged [315] (by decide) (by decide)
 intro gone
 have even := ConsumedParity11.consumed_even logged completed [315] (by decide) (by decide) gone
 have zero : energy soko1_1.initial final [315] outcomes=0 := by omega
 have moved : ownPushes [315] outcomes≠0 := by
   intro fixed
   have tag := no_push_unchanged [315] outcomes fixed
   rw [gone] at tag
   contradiction
 have positive := moved_positive logged moved
 omega

theorem at_most_one {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤326) : ownPushes [315] outcomes≤1 := by
 have survives := survives logged completed cheap
 have ledger := survivor_energy logged completed 315 survives
 have initial : value soko1_1.initial [315]=0 := by decide +kernel
 obtain ⟨_,_,_,rest⟩ := Tight32611.budgets logged completed cheap
 have compare := energy_subset (Trace.nil soko1_1.initial) logged [315] UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [initial] at ledger
 simp only [Int.ofNat_eq_natCast] at ledger
 omega
#print axioms prices
#print axioms moved_positive
#print axioms survives
#print axioms at_most_one
end Owner1007.Spare31511
