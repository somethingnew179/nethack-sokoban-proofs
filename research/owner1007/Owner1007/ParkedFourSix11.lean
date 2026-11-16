import Owner1007.ParkedPivot11
import Owner1007.Upper190After11
import Owner1007.UpperSixExit11
import Owner1007.Paid137Six11
import Owner1007.QuietFixed11
import Owner1007.LoggedEventGap11
import Owner1007.UpperConsumedFuture11
namespace Owner1007.ParkedFourSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem absurd {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 189)))
 (cheap : energy soko1_1.initial final U6 outcomes<6)
 (parked : OwnedCorral11.Good Parked18811.locks Parked18811.region cut.actor.state
   (update (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome)) : False := by
 have cheap137 : energy soko1_1.initial final [137] outcomes<2 := by
   by_cases paid : 2≤energy soko1_1.initial final [137] outcomes
   · have contradiction := Paid137Six11.upper_six logged completed paid
     omega
   · omega
 obtain ⟨initial137,initial139⟩ := Upper190History11.FirstCut.stationary_before_190west cut sourceEq directionEq
 let group := update (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 190 (.stay 189)) cut.headEffect effect
 have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
 have reached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have selectedBefore := cut.before.logged.end_subset (by decide) Upper190After11.group (by decide) (by decide)
 have groupUnique := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ selectedBefore.1 selectedBefore.2
 have groupInside := GhostSubset.update_subset _ _ _ cut.headEffect _ selectedBefore.1 selectedBefore.2
 have beforeSize := endGroup_length_le Upper190After11.group cut.beforeOutcomes
 have groupSize : group.length≤4 := Nat.le_trans (update_length _ _) beforeSize
 have bigFacts := UpperCutBudget11.next_facts cut
 have tailBudget := UpperSixBudget11.two_tail_le cut
 have beforeInclude := end_subset_selected cut.before.logged (by decide) Upper190After11.group U6 (by decide) (by decide) (by decide) (by decide)
 have groupInclude := update_mono _ _ selectedBefore.1 beforeInclude cut.headOutcome
 have tailCompare := energy_subset reached cut.after group (UpperCutBudget11.nextGroup cut) groupUnique bigFacts.1 groupInclude bigFacts.2.1 bigFacts.2.2
 have cheapTail : energy cut.actor.state final group cut.afterOutcomes<4 := by omega
 have allGone := UpperCheapConsumed11.all_gone logged completed cheap
 have mono := logged.end_mono (by decide) Upper190After11.group U6 (by decide) (by decide) (by decide)
 rw [allGone] at mono
 have gone : endGroup Upper190After11.group outcomes=[] :=
   List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using mono member)
 have oldEffects : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
   calc
     _=cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes := by simp only [List.append_assoc,List.cons_append,List.nil_append]
     _=outcomes := cut.outcomesEq.symm
 rw [←oldEffects,endGroup_append] at gone
 have groupGone : endGroup group cut.afterOutcomes=[] := by
   simpa only [endGroup_append,endGroup] using gone
 obtain ⟨useful⟩ := ParkedPivot11.first_cut reached cut.after completed group groupUnique groupInside groupSize parked
 have currentGood := PairFirstCut11.quiet_good ParkedPivot11.closed Parked18811.unique Parked18811.size useful.before
   valid.1 groupUnique groupInside groupSize parked reached.holes_sublist.subset
 have currentSelected := useful.before.logged.end_subset valid.1 group groupUnique groupInside
 have currentSize := endGroup_length_le group useful.beforeOutcomes
 have currentBound : (endGroup group useful.beforeOutcomes).length≤4 := Nat.le_trans currentSize groupSize
 have currentReached := reached.append useful.before.logged.trace
 have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
 obtain ⟨source,owner,metadata,shape⟩ := ParkedPivot11.head_shape currentGood currentSelected.2 currentBound useful.headChecked useful.headPaid
 have isExit : ParkedActor11.Exit source useful.direction := by
   rcases shape with h|h|h|h <;> simp_all [ParkedActor11.Exit]
 have headCost := ParkedStrict11.exit_row scalar rfl currentValid useful.headChecked useful.headEffect currentSelected.1 currentSelected.2
   ⟨source,owner,metadata,isExit⟩
 change 2≤RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome at headCost
 let firstHead : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
 let toState := cut.before.logged.append firstHead
 let toCurrent := toState.append useful.before.logged
 have allEffects : ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)++useful.headOutcome::useful.afterOutcomes=outcomes := by
   calc
     _=cut.beforeOutcomes++cut.headOutcome::(useful.beforeOutcomes++useful.headOutcome::useful.afterOutcomes) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
     _=cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes := congrArg (fun rest => cut.beforeOutcomes++cut.headOutcome::rest) useful.outcomesEq.symm
     _=outcomes := cut.outcomesEq.symm
 have stateFixed : ∀c∈[137,139], ownPushes [c] (cut.beforeOutcomes++[cut.headOutcome])=0 := by
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   · rw [ownPushes_append,no_push_unchanged _ _ initial137,headEq]
     simpa [ownPushes,ownPush] using initial137
   · rw [ownPushes_append,no_push_unchanged _ _ initial139,headEq]
     simpa [ownPushes,ownPush] using initial139
 have currentFixed : ∀c∈[137,139], ownPushes [c] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)=0 := by
   intro c member
   have initialZero := stateFixed c member
   obtain ⟨node,_,selected⟩ := parked
   have inLocks : c∈Parked18811.locks node := by
     have all : (List.finRange 9).all (fun i => decide (([137,139] : List Cell)⊆Parked18811.locks i))=true := by decide +kernel
     exact of_decide_eq_true (List.all_eq_true.mp all node (by simp)) member
   have inGroup : c∈group := selected inLocks
   have tailZero := useful.before.fixed inGroup (fun dir => by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> simp [ParkedPivot11.paid])
   rw [ownPushes_append,no_push_unchanged _ _ initialZero,tailZero,initialZero]
 have currentActual := step_boulders_nodup _ _ _ _ currentValid.1 useful.headChecked
 have nextUnique := GhostSubset.update_unique _ _ _ useful.headEffect currentActual _ currentSelected.1 currentSelected.2
 have nextInside := GhostSubset.update_subset _ _ _ useful.headEffect _ currentSelected.1 currentSelected.2
 have nextBound := Nat.le_trans (update_length (endGroup group useful.beforeOutcomes) useful.headOutcome) currentBound
 have prefixNN := HeroLedger.Logged.energy_nonnegative useful.before.logged (groupCertificate 4) valid group groupUnique groupInside groupSize
 change 0≤energy cut.actor.state useful.middle group useful.beforeOutcomes at prefixNN
 have split := energy_append cut.actor.state useful.middle final group useful.beforeOutcomes (useful.headOutcome::useful.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight useful.middle useful.actor.state final
   (endGroup group useful.beforeOutcomes) useful.headOutcome useful.afterOutcomes
 change energy useful.middle final (endGroup group useful.beforeOutcomes) (useful.headOutcome::useful.afterOutcomes)=
   RankedCorral11.gap useful.middle useful.actor (endGroup group useful.beforeOutcomes) useful.headOutcome+
   energy useful.actor.state final (update (endGroup group useful.beforeOutcomes) useful.headOutcome) useful.afterOutcomes at one
 have excludeSide : ParkedPivot11.Side source useful.direction → False := by
   intro side
   have nextGood := ParkedPivot11.enter_cover currentGood currentSelected.2 currentBound currentReached.holes_sublist.subset
     useful.headChecked useful.headEffect ⟨source,owner,metadata,side⟩
   have nextReached := currentReached.append (Trace.cons useful.headChecked (Trace.nil useful.actor.state))
   have nextGone : endGroup (update (endGroup group useful.beforeOutcomes) useful.headOutcome) useful.afterOutcomes=[] := by
     have rewritten := groupGone
     rw [useful.outcomesEq,endGroup_append] at rewritten
     exact rewritten
   have future := Upper187Cover11.future_energy nextReached useful.after _ nextUnique nextInside (by omega) nextGood nextGone
   rw [useful.outcomesEq] at cheapTail
   omega
 rcases shape with ⟨rfl,usefulDir⟩|⟨rfl,usefulDir⟩|⟨rfl,usefulDir⟩|⟨rfl,usefulDirs⟩
 · have zero := currentFixed 137 (by decide)
   have tag := no_push_unchanged _ _ zero
   have singleton := toCurrent.end_subset (by decide) [137] (by decide) (by decide)
   have row := CutStrict11.exit_row scalar rfl currentValid useful.headChecked useful.headEffect singleton.1 singleton.2
     ⟨137,by rw [tag]; simp,metadata,by simp [CutActor11.Exit,usefulDir]⟩
   have bound := logged_event_gap_le toCurrent useful.headChecked useful.headEffect useful.after [137] (by decide) (by decide)
   rw [allEffects] at bound
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) useful.headOutcome+
     value useful.actor.state (update (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) useful.headOutcome)-
     value useful.middle (endGroup [137] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)) at row
   omega
 · have zero := currentFixed 139 (by decide)
   have checked : step soko1_1.board useful.middle .east=some useful.actor := by simpa only [usefulDir] using useful.headChecked
   have usefulHead := UpperHeadCases11.ordinary_effect checked useful.headEffect metadata
     (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) currentReached.holes_sublist.subset
   have usefulEffect : Matches useful.middle useful.actor (.push 139 (.stay 140)) := by simpa only [usefulHead] using useful.headEffect
   have cheap141 := UpperSixBudget11.cheap_others_four logged completed cheap 141 (by decide)
   have prefixBound := prefix_energy_le toCurrent (Logged.cons useful.headChecked useful.headEffect useful.after) [141] (by decide) (by decide)
   rw [allEffects] at prefixBound
   have prefixCheap : energy soko1_1.initial useful.middle [141] ((cut.beforeOutcomes++[cut.headOutcome])++useful.beforeOutcomes)<6 := by omega
   have survives := StationaryExitSix11.survives139 toCurrent checked usefulEffect useful.after zero prefixCheap
   have allEffects' := allEffects
   rw [usefulHead] at allEffects'
   have full : endGroup [139] outcomes≠[] := by rw [←allEffects']; exact survives
   exact UpperSixExit11.survivor_six_absurd logged completed cheap 139 (by decide) full
 · exact excludeSide (by simp [ParkedPivot11.Side,usefulDir])
 · exact excludeSide (by simp [ParkedPivot11.Side,usefulDirs])
#print axioms absurd
end Owner1007.ParkedFourSix11
