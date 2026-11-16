import Owner1007.WestRankInitial11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
import Owner1007.LoggedEventGap11
import Owner1007.UpperSixExit11
import Owner1007.Paid137Six11
namespace Owner1007.Upper138WestSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 138) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 138 (.stay 137))) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have cheap137 : energy soko1_1.initial final [137] outcomes<2 := by
     by_cases paid : 2≤energy soko1_1.initial final [137] outcomes
     · have contradiction := Paid137Six11.upper_six logged completed paid
       omega
     · omega
   obtain ⟨i,initialHero,initialLocks,initialMarker,initialRank,initial191⟩ :=
     WestRankInitial11.after138west cut sourceEq directionEq effect cheap137
   let group := update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome
   have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 138 (.stay 137)) cut.headEffect effect
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have reached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have selectedBefore := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
   have groupUnique := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ selectedBefore.1 selectedBefore.2
   have groupInside := GhostSubset.update_subset _ _ _ cut.headEffect _ selectedBefore.1 selectedBefore.2
   have beforeSize := endGroup_length_le originalGroup cut.beforeOutcomes
   have groupSize : group.length≤3 := by
     change (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome).length≤3
     exact Nat.le_trans (update_length _ _) beforeSize
   have bigFacts := UpperCutBudget11.next_facts cut
   have tailBudget := UpperSixBudget11.two_tail_le cut
   have beforeInclude := end_subset_selected cut.before.logged (by decide) originalGroup U6 (by decide) (by decide) (by decide) (by decide)
   have groupInclude := update_mono _ _ selectedBefore.1 beforeInclude cut.headOutcome
   have tailCompare := energy_subset reached cut.after group (UpperCutBudget11.nextGroup cut) groupUnique bigFacts.1 groupInclude bigFacts.2.1 bigFacts.2.2
   have cheapTail : energy cut.actor.state final group cut.afterOutcomes<4 := by omega
   have good : OwnedCorral11.Good WestRank11.locks WestRank11.region cut.actor.state group := ⟨i,initialHero,initialLocks⟩
   obtain ⟨useful⟩ := WestRankHead11.first_cut reached cut.after completed group groupUnique groupInside groupSize good
   obtain ⟨j,currentHero,currentLocks,markerTrace,rankBound⟩ := RankedCorral11.quiet_rank WestRank11.closed WestRank11.unique WestRank11.size
     WestRank11.marker_inside WestRank11.refined useful.before valid groupUnique groupInside groupSize i initialHero initialLocks reached.holes_sublist.subset
   have currentSelected := useful.before.logged.end_subset valid.1 group groupUnique groupInside
   have currentSize := endGroup_length_le group useful.beforeOutcomes
   have currentBound : (endGroup group useful.beforeOutcomes).length≤3 := by omega
   have currentReached := reached.append useful.before.logged.trace
   have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
   obtain ⟨source,owner,metadata,shape⟩ := WestRankHead11.head_shape j currentHero currentLocks currentSelected.2 currentBound useful.headChecked useful.headPaid
   have currentSourceLock := WestRankHead11.lock_complete j _ currentBound currentLocks source owner
   let firstHead : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
     .cons cut.headChecked cut.headEffect (.nil _)
   let toState := cut.before.logged.append firstHead
   let toCurrent := toState.append useful.before.logged
   have allEffects : ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)++useful.headOutcome::useful.afterOutcomes=outcomes := by
     calc
       _ = cut.beforeOutcomes++cut.headOutcome::(useful.beforeOutcomes++useful.headOutcome::useful.afterOutcomes) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
       _ = cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes := congrArg (fun rest => cut.beforeOutcomes++cut.headOutcome::rest) useful.outcomesEq.symm
       _ = outcomes := cut.outcomesEq.symm
   have initial191Tag : endGroup [191] cut.beforeOutcomes=[191] := no_push_unchanged _ _ initial191
   have state191 : ownPushes [191] (cut.beforeOutcomes++[cut.headOutcome])=0 := by
     rw [ownPushes_append,initial191Tag,headEq]
     simpa [ownPushes,ownPush] using initial191
   have state191Tag : endGroup [191] (cut.beforeOutcomes++[cut.headOutcome])=[191] := no_push_unchanged _ _ state191
   have inGroup191 : 191∈group := by
     have all : ∀i, 191∈WestRank11.locks i := by decide +kernel
     exact initialLocks (all i)
   have quiet191 := useful.before.fixed inGroup191 (fun dir => by simp [WestRank11.paid])
   have current191 : ownPushes [191] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)=0 := by
     rw [ownPushes_append,state191Tag,quiet191,state191]
   have stateMarker : endGroup [137] (cut.beforeOutcomes++[cut.headOutcome])=[WestRank11.marker i] := by
     rw [endGroup_append]
     simpa only [endGroup] using initialMarker
   have currentMarker : endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)=[WestRank11.marker j] := by
     rw [endGroup_append,stateMarker]
     exact markerTrace
   have currentActual := step_boulders_nodup _ _ _ _ currentValid.1 useful.headChecked
   have nextUnique := GhostSubset.update_unique _ _ _ useful.headEffect currentActual _ currentSelected.1 currentSelected.2
   have nextInside := GhostSubset.update_subset _ _ _ useful.headEffect _ currentSelected.1 currentSelected.2
   have nextBound := Nat.le_trans (update_length (endGroup group useful.beforeOutcomes) useful.headOutcome) currentBound
   have nextValid := (groupCertificate 3).preserved _ _ _ currentValid useful.headChecked
   have tailNN := HeroLedger.Logged.energy_nonnegative useful.after (groupCertificate 3) nextValid
     _ nextUnique nextInside nextBound
   change 0≤energy useful.actor.state final (update (endGroup group useful.beforeOutcomes) useful.headOutcome) useful.afterOutcomes at tailNN
   have split := energy_append cut.actor.state useful.middle final group useful.beforeOutcomes (useful.headOutcome::useful.afterOutcomes)
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight useful.middle useful.actor.state final
     (endGroup group useful.beforeOutcomes) useful.headOutcome useful.afterOutcomes
   change energy useful.middle final (endGroup group useful.beforeOutcomes) (useful.headOutcome::useful.afterOutcomes)=
     RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome+
     energy useful.actor.state final (update (endGroup group useful.beforeOutcomes) useful.headOutcome) useful.afterOutcomes at one
   have excludeRanked : WestRank11.rank j=2 →
       2≤RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome → False := by
     intro rankTwo headTwo
     rw [initialRank] at rankBound
     rw [useful.outcomesEq] at cheapTail
     omega
   rcases shape with ⟨rfl,usefulDir,rankTwo⟩|⟨rfl,usefulDir,rankTwo⟩|⟨rfl,usefulDir⟩|⟨rfl,usefulDir⟩
   · have checked : step soko1_1.board useful.middle .west=some useful.actor := by simpa only [usefulDir] using useful.headChecked
     have row := WestRankHead11.row136 currentValid checked useful.headEffect metadata owner currentSelected.1 currentSelected.2
     exact False.elim (excludeRanked rankTwo row)
   · have row := CutStrict11.exit_row scalar rfl currentValid useful.headChecked useful.headEffect currentSelected.1 currentSelected.2
       ⟨139,owner,metadata,by simp [CutActor11.Exit,usefulDir]⟩
     change 2≤RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome at row
     exact False.elim (excludeRanked rankTwo row)
   · have checked : step soko1_1.board useful.middle .east=some useful.actor := by simpa only [usefulDir] using useful.headChecked
     have usefulHead := UpperHeadCases11.ordinary_effect checked useful.headEffect metadata
       (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) currentReached.holes_sublist.subset
     have usefulEffect : Matches useful.middle useful.actor (.push 191 (.stay 192)) := by simpa only [usefulHead] using useful.headEffect
     have cheap193 := UpperSixBudget11.cheap_others_four logged completed cheap 193 (by decide)
     have prefixBound := prefix_energy_le toCurrent (Logged.cons useful.headChecked useful.headEffect useful.after) [193] (by decide) (by decide)
     rw [allEffects] at prefixBound
     have prefixCheap : energy soko1_1.initial useful.middle [193] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)<6 := by omega
     have survives := StationaryExitSix11.survives191 toCurrent checked usefulEffect useful.after current191 prefixCheap
     have allEffects' := allEffects
     rw [usefulHead] at allEffects'
     have full : endGroup [191] outcomes≠[] := by rw [←allEffects']; exact survives
     exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 191 (by decide) full)
   · have marker216 := WestRankHead11.marker216 j currentSourceLock
     rw [marker216] at currentMarker
     have currentSingleton := toCurrent.end_subset (by decide) [137] (by decide) (by decide)
     have row := CutStrict11.exit_row scalar rfl currentValid useful.headChecked useful.headEffect currentSingleton.1 currentSingleton.2
       ⟨216,by rw [currentMarker]; simp,metadata,by simp [CutActor11.Exit,usefulDir]⟩
     change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) useful.headOutcome+
       value useful.actor.state (update (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) useful.headOutcome)-
       value useful.middle (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) at row
     have bound := logged_event_gap_le toCurrent useful.headChecked useful.headEffect useful.after [137] (by decide) (by decide)
     rw [allEffects] at bound
     omega
#print axioms upper_six
end Owner1007.Upper138WestSix11
