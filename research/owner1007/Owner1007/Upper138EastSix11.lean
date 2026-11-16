import Owner1007.WestRankEastInitial11
import Owner1007.WestBudgetReturn11
import Owner1007.UpperResetGuards11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11
import Owner1007.LoggedEventGap11
import Owner1007.UpperSixExit11
import Owner1007.Paid137Six11
namespace Owner1007.Upper138EastSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 138) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 138 (.stay 139))) :
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
     WestRankEastInitial11.after138east cut sourceEq directionEq effect cheap137
   let group := update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome
   have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 138 (.stay 139)) cut.headEffect effect
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
   have no136Before : 136∉endGroup originalGroup cut.beforeOutcomes := by
     have oldGood := quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
       original_good (by simp)
     obtain ⟨oldIndex,_,kept⟩ := oldGood
     intro found
     have member := UpperQuiet11.lock_complete oldIndex _ beforeSize kept 136 found
     exact (show ∀ k : Fin 19, (136:Cell)∉UpperZero11.locks k from by decide +kernel) oldIndex member
   have owner138 : 138∈endGroup originalGroup cut.beforeOutcomes := by
     obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
     have same : source=138 := Option.some.inj (metadata.symm.trans sourceEq)
     exact same ▸ owner
   have no136 : 136∉group := by
     change 136∉update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     simp only [update,move,if_pos owner138,post]
     intro found
     rcases List.mem_cons.mp found with impossible|old
     · exact (by decide : (136:Cell)≠139) impossible
     · exact no136Before (List.mem_of_mem_erase old)
   have group139 : 139∈group := by
     change 139∈update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome
     rw [headEq]
     simp only [update,move,if_pos owner138,post,List.mem_cons,true_or]
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
   have initial139 := UpperResetHistory11.before138east cut sourceEq directionEq effect cheap137
   have state139Tag : endGroup [139] (cut.beforeOutcomes++[cut.headOutcome])=[139] := by
     rw [endGroup_append,initial139.2,headEq]
     rfl
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
   have excludePaid : 2≤energy cut.actor.state useful.middle group useful.beforeOutcomes →
       2≤RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome → False := by
     intro paidPrefix headTwo
     rw [useful.outcomesEq] at cheapTail
     omega
   rcases shape with ⟨rfl,usefulDir,rankTwo⟩|⟨rfl,usefulDir,rankTwo⟩|⟨rfl,usefulDir⟩|⟨rfl,usefulDir⟩
   · have checked : step soko1_1.board useful.middle .west=some useful.actor := by simpa only [usefulDir] using useful.headChecked
     have row := WestRankHead11.row136 currentValid checked useful.headEffect metadata owner currentSelected.1 currentSelected.2
     by_cases paidPrefix : 2≤energy cut.actor.state useful.middle group useful.beforeOutcomes
     · exact False.elim (excludePaid paidPrefix row)
     · have low : energy cut.actor.state useful.middle group useful.beforeOutcomes<2 := by omega
       have avoid := WestBudgetReturn11.no_return reached useful.before.logged group groupUnique groupInside groupSize good low 136 (by simp)
       have old := OneWayToken11.historical useful.before.logged valid.1 136 group groupUnique groupInside avoid owner
       exact False.elim (no136 old.1)
   · have row := CutStrict11.exit_row scalar rfl currentValid useful.headChecked useful.headEffect currentSelected.1 currentSelected.2
       ⟨139,owner,metadata,by simp [CutActor11.Exit,usefulDir]⟩
     change 2≤RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome at row
     by_cases paidPrefix : 2≤energy cut.actor.state useful.middle group useful.beforeOutcomes
     · exact False.elim (excludePaid paidPrefix row)
     · have low : energy cut.actor.state useful.middle group useful.beforeOutcomes<2 := by omega
       have avoid := WestBudgetReturn11.no_return reached useful.before.logged group groupUnique groupInside groupSize good low 139 (by simp)
       have history := OneWayToken11.historical useful.before.logged valid.1 139 group groupUnique groupInside avoid owner
       have checked : step soko1_1.board useful.middle .east=some useful.actor := by simpa only [usefulDir] using useful.headChecked
       have usefulHead := UpperHeadCases11.ordinary_effect checked useful.headEffect metadata
         (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) currentReached.holes_sublist.subset
       have usefulEffect : Matches useful.middle useful.actor (.push 139 (.stay 140)) := by simpa only [usefulHead] using useful.headEffect
       have fullCheap141 := UpperResetBudget11.cheap_c_two logged completed cut 0 sourceEq directionEq effect cheap 141 (by decide)
       have prefixBound := prefix_energy_le toCurrent (Logged.cons useful.headChecked useful.headEffect useful.after) [141] (by decide) (by decide)
       rw [allEffects] at prefixBound
       have prefixCheap141 : energy soko1_1.initial useful.middle [141]
           ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)<2 := by omega
       have clamp := UpperResetGuards11.before141_reset logged completed cut sourceEq directionEq effect cheap
       have initialMate : ∃ box : Cell, box∈([141,140] : List Cell) ∧
           endGroup [141] (cut.beforeOutcomes++[cut.headOutcome])=[box] := by
         rcases clamp with normal|shifted
         · refine ⟨141,by simp,?_⟩
           rw [endGroup_append,normal,headEq]
           rfl
         · refine ⟨140,by simp,?_⟩
           rw [endGroup_append,shifted,headEq]
           rfl
       obtain ⟨box,boxMember,boxTag⟩ := initialMate
       have stateMate := toState.end_subset (by decide) [141] (by decide) (by decide)
       have boxPresent : box∈cut.actor.state.boulders := stateMate.2 (by rw [boxTag]; simp)
       have initial139Actual : 139∈cut.actor.state.boulders := groupInside group139
       have pastNN := energy_nonnegative toState [141] (by decide) (by decide)
       have splitMate := energy_append soko1_1.initial cut.actor.state useful.middle [141]
         (cut.beforeOutcomes++[cut.headOutcome]) useful.beforeOutcomes
       rw [boxTag] at splitMate
       have localCheap : energy cut.actor.state useful.middle [box] useful.beforeOutcomes<2 := by omega
       obtain ⟨mate,mateMember,mateTag⟩ := StationaryGuards11.guard_logged StationaryGuards11.guards141 useful.before.logged
         valid initial139Actual boxPresent boxMember history.2 localCheap
       obtain ⟨result,_,push⟩ := effect_push_data checked usefulEffect
       obtain ⟨dest,adjacent,_,_,empty⟩ := (push_first_clear soko1_1.board useful.middle 139 .east result push).2
       have destEq : dest=140 := Option.some.inj (adjacent.symm.trans (by decide +kernel))
       have clear140 : 140∉useful.middle.boulders := destEq ▸ empty
       have actualMate := useful.before.logged.end_subset valid.1 [box] (by simp) (by simpa using boxPresent)
       have mate141 : 141∈useful.middle.boulders := by
         rcases List.mem_cons.mp mateMember with normal|shifted
         · exact actualMate.2 (by rw [mateTag,normal]; simp)
         · have same : mate=140 := List.mem_singleton.mp shifted
           exact False.elim (clear140 (actualMate.2 (by rw [mateTag,same]; simp)))
       have pairInside : ([140,141] : List Cell)⊆useful.actor.state.boulders := by
         rw [usefulEffect.2]
         intro cell found
         rcases List.mem_cons.mp found with rfl|later
         · simp
         · have same : cell=141 := List.mem_singleton.mp later
           subst cell
           exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 141≠139)).mpr mate141)
       have fixed140 := locked_identity useful.after (Owner1007.locked_of_check _ [140,141] (by decide +kernel))
         pairInside (show 140∈([140,141] : List Cell) by simp)
       have localSurvives : endGroup [139] (useful.beforeOutcomes++ .push 139 (.stay 140)::useful.afterOutcomes)≠[] := by
         rw [endGroup_append,no_push_unchanged _ _ history.2]
         change endGroup [140] useful.afterOutcomes≠[]
         rw [fixed140]
         simp
       have allEffects' := allEffects
       rw [usefulHead] at allEffects'
       have shapeAll : outcomes=(cut.beforeOutcomes++[cut.headOutcome])++
           (useful.beforeOutcomes++ .push 139 (.stay 140)::useful.afterOutcomes) := by
         exact allEffects'.symm.trans (List.append_assoc _ _ _)
       have full : endGroup [139] outcomes≠[] := by
         rw [shapeAll,endGroup_append,state139Tag]
         exact localSurvives
       exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 139 (by decide) full)
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
end Owner1007.Upper138EastSix11
