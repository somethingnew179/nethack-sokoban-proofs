import Owner1007.Upper190ResetState11
import Owner1007.Upper190Parked11
import Owner1007.UpperLocal19011
import Owner1007.UpperLocalBudget11
import Owner1007.UpperConsumedFuture11
import Owner1007.GuardedExit11
import Owner1007.ParkedEnergy11
import Owner1007.LoggedEventGap11
import Owner1007.Paid137Six11
namespace Owner1007.Upper190EastSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (first : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : first.actor.pushSource=some 190) (directionEq : first.direction=.east)
 (effect : Matches first.middle first.actor (.push 190 (.stay 191))) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have cheap137 : energy soko1_1.initial final [137] outcomes<2 := by
     by_cases paid : 2≤energy soko1_1.initial final [137] outcomes
     · have six := Paid137Six11.upper_six logged completed paid
       omega
     · omega
   let small := update (endGroup originalGroup first.beforeOutcomes) first.headOutcome
   let big := UpperCutBudget11.nextGroup first
   have headEq := GhostProjection.matches_unique first.middle first.actor first.headOutcome (.push 190 (.stay 191)) first.headEffect effect
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace
   have actual := step_boulders_nodup _ _ _ _ beforeValid.1 first.headChecked
   have reached := first.before.logged.trace.append (Trace.cons first.headChecked (Trace.nil first.actor.state))
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have selected := first.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
   have smallUnique := GhostSubset.update_unique _ _ _ first.headEffect actual _ selected.1 selected.2
   have smallInside := GhostSubset.update_subset _ _ _ first.headEffect _ selected.1 selected.2
   have beforeBound := endGroup_length_le originalGroup first.beforeOutcomes
   have smallBound : small.length≤3 := Nat.le_trans (update_length _ _) beforeBound
   have shapeSmall := (Upper190ResetState11.before_after first sourceEq directionEq effect).2
   have goodStart : OwnedCorral11.Good UpperZero11.locks UpperZero11.region first.actor.state small := by
     refine ⟨0,?_,?_⟩
     · have hero : first.actor.state.player=190 := by rw [effect.2]
       rw [hero]; decide +kernel
     · intro c member
       exact shapeSmall.mem_iff.mpr member
   have bigFacts := UpperCutBudget11.next_facts first
   have includedBefore := end_subset_selected first.before.logged (by decide) originalGroup U6 (by decide) (by decide) (by decide) (by decide)
   have included := update_mono _ _ selected.1 includedBefore first.headOutcome
   have firstBudget := UpperSixBudget11.two_tail_le first
   change 2+energy first.actor.state final big first.afterOutcomes≤energy soko1_1.initial final U6 outcomes at firstBudget
   have cheapBig : energy first.actor.state final big first.afterOutcomes<4 := by omega
   obtain ⟨later⟩ := UpperLocalCuts11.first_cut reached first.after completed small smallUnique smallInside smallBound goodStart
   have currentReached := reached.append later.before.logged.trace
   have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
   have currentActual := step_boulders_nodup _ _ _ _ currentValid.1 later.headChecked
   have nextReached := currentReached.append (Trace.cons later.headChecked (Trace.nil later.actor.state))
   have localFacts := UpperLocalBudget11.next_facts later reached big bigFacts.1 bigFacts.2.1 bigFacts.2.2
   have localBudget := UpperLocalBudget11.two_tail_le later reached smallUnique big bigFacts.1 bigFacts.2.1 bigFacts.2.2 included
   have cheapNext : energy later.actor.state final (UpperLocalBudget11.next later big) later.afterOutcomes<2 := by omega
   have cap : ∀ cells : List Cell, cells.Nodup → cells⊆UpperLocalBudget11.next later big →
       energy later.actor.state final cells later.afterOutcomes<2 := by
     intro cells unique subset
     have compare := energy_subset nextReached later.after cells (UpperLocalBudget11.next later big)
       unique localFacts.1 subset localFacts.2.1 localFacts.2.2
     omega
   have localBefore := later.before.logged.end_subset valid.1 small smallUnique smallInside
   have nextSmallUnique := GhostSubset.update_unique _ _ _ later.headEffect currentActual _ localBefore.1 localBefore.2
   have nextSmallInside := GhostSubset.update_subset _ _ _ later.headEffect _ localBefore.1 localBefore.2
   have localBeforeBound := Nat.le_trans (endGroup_length_le small later.beforeOutcomes) smallBound
   have nextSmallBound := Nat.le_trans (update_length (endGroup small later.beforeOutcomes) later.headOutcome) localBeforeBound
   have localInclude := end_subset_selected later.before.logged valid.1 small big smallUnique bigFacts.1 included bigFacts.2.1
   have nextInclude := update_mono _ _ localBefore.1 localInclude later.headOutcome
   have excludeReset : OwnedCorral11.Good UpperZero11.locks UpperZero11.region later.actor.state
       (update (endGroup small later.beforeOutcomes) later.headOutcome) → False := by
     intro good
     have price := CutEnergy11.future_energy UpperZero11.closed UpperZero11.unique UpperZero11.size
       (by decide) CutEnergy11.upper_paid nextReached later.after completed _ nextSmallUnique nextSmallInside nextSmallBound good
     have less := cap _ nextSmallUnique nextInclude
     omega
   let firstHead : Logged soko1_1.board first.middle [first.direction] first.actor.state first.actor.pushCost 1 [first.headOutcome] :=
     .cons first.headChecked first.headEffect (.nil _)
   let toState := first.before.logged.append firstHead
   let toCurrent := toState.append later.before.logged
   have allEffects : ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)++later.headOutcome::later.afterOutcomes=outcomes := by
     calc
       _ = first.beforeOutcomes++first.headOutcome::(later.beforeOutcomes++later.headOutcome::later.afterOutcomes) := by
         simp only [List.append_assoc,List.cons_append,List.nil_append]
       _ = first.beforeOutcomes++first.headOutcome::first.afterOutcomes :=
         congrArg (fun rest=>first.beforeOutcomes++first.headOutcome::rest) later.outcomesEq.symm
       _ = outcomes := first.outcomesEq.symm
   have startSmall : endGroup originalGroup (first.beforeOutcomes++[first.headOutcome])=small := by
     rw [endGroup_append]
     rfl
   have startBig : endGroup U6 (first.beforeOutcomes++[first.headOutcome])=big := by
     rw [endGroup_append]
     rfl
   have allGone := UpperCheapConsumed11.all_gone logged completed cheap
   have stateGone : endGroup big first.afterOutcomes=[] := by
     rw [first.outcomesEq,endGroup_append] at allGone
     exact allGone
   have nextGone : endGroup (UpperLocalBudget11.next later big) later.afterOutcomes=[] := by
     rw [later.outcomesEq,endGroup_append] at stateGone
     exact stateGone
   have goneSmall : ∀ cells : List Cell, cells.Nodup → cells⊆UpperLocalBudget11.next later big →
       endGroup cells later.afterOutcomes=[] := by
     intro cells unique subset
     have actualInside := List.Subset.trans subset localFacts.2.1
     have mono := later.after.end_mono currentActual cells (UpperLocalBudget11.next later big) unique actualInside subset
     rw [nextGone] at mono
     exact List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using mono member)
   have initialStill := Upper190ResetState11.stationary_before first sourceEq directionEq effect
   have state137 : ownPushes [137] (first.beforeOutcomes++[first.headOutcome])=0 := by
     rw [ownPushes_append,no_push_unchanged _ _ initialStill.1,headEq]
     simpa [ownPushes,ownPush] using initialStill.1
   have tag137 : endGroup [137] (first.beforeOutcomes++[first.headOutcome])=[137] := no_push_unchanged _ _ state137
   have state139 : ownPushes [139] (first.beforeOutcomes++[first.headOutcome])=0 := by
     rw [ownPushes_append,no_push_unchanged _ _ initialStill.2,headEq]
     simpa [ownPushes,ownPush] using initialStill.2
   have tag139 : endGroup [139] (first.beforeOutcomes++[first.headOutcome])=[139] := no_push_unchanged _ _ state139
   have history191 := UpperResetHistory11.before190east first sourceEq directionEq effect cheap137
   have tag191 : endGroup [191] (first.beforeOutcomes++[first.headOutcome])=[191] := by
     rw [endGroup_append,history191.2,headEq]
     rfl
   have stationary (cell : Cell) (member : cell∈[137,139,191])
       (metadata : later.actor.pushSource=some cell) : ownPushes [cell] later.beforeOutcomes=0 := by
     obtain ⟨source,owner,record,_⟩ := later.headPaid
     have same : source=cell := Option.some.inj (record.symm.trans metadata)
     have present : cell∈endGroup small later.beforeOutcomes := same ▸ owner
     exact later.before.stationary UpperZero11.closed valid.1 smallUnique smallInside smallBound goodStart
       reached.holes_sublist.subset cell member present
   have localCheap (cell box : Cell) (member : cell∈C)
       (tag : endGroup [cell] (first.beforeOutcomes++[first.headOutcome])=[box]) :
       energy first.actor.state later.middle [box] later.beforeOutcomes<2 := by
     have singletonInside : [cell]⊆soko1_1.initial.boulders := by
       intro c found
       have same : c=cell := List.mem_singleton.mp found
       exact same ▸ (show C⊆soko1_1.initial.boulders from by decide) member
     have cheapCell := UpperResetBudget11.cheap_c_two logged completed first 1 sourceEq directionEq effect cheap cell member
     have prefixBound := prefix_energy_le toCurrent (Logged.cons later.headChecked later.headEffect later.after)
       [cell] (by simp) singletonInside
     rw [allEffects] at prefixBound
     have nn := energy_nonnegative toState [cell] (by simp) singletonInside
     have split := energy_append soko1_1.initial first.actor.state later.middle [cell]
       (first.beforeOutcomes++[first.headOutcome]) later.beforeOutcomes
     rw [tag] at split
     omega
   rcases UpperLocalCuts11.head_cases later reached with
     ⟨dirEq,srcEq,head⟩ | ⟨dirEq,srcEq,head⟩ | ⟨dirEq,srcEq,head⟩ |
     ⟨dirEq,srcEq,head⟩ | ⟨dirEq,srcEq,head⟩ | ⟨dirEq,srcEq,head⟩ |
     ⟨dirEq,srcEq,head⟩ | ⟨dirEq,srcEq,head⟩
   · have still := stationary 137 (by simp) srcEq
     have currentTag : endGroup [137] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)=[137] := by
       rw [endGroup_append,tag137,no_push_unchanged _ _ still]
     have currentSingleton := toCurrent.end_subset (by decide) [137] (by decide) (by decide)
     have row := CutStrict11.exit_row scalar rfl currentValid later.headChecked later.headEffect currentSingleton.1 currentSingleton.2
       ⟨137,by rw [currentTag]; simp,srcEq,by simp [CutActor11.Exit,dirEq]⟩
     change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [137] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)) later.headOutcome+
       value later.actor.state (update (endGroup [137] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)) later.headOutcome)-
       value later.middle (endGroup [137] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)) at row
     have bound := logged_event_gap_le toCurrent later.headChecked later.headEffect later.after [137] (by decide) (by decide)
     rw [allEffects] at bound
     omega
   · have still := stationary 139 (by simp) srcEq
     have checked : step soko1_1.board later.middle .east=some later.actor := by simpa only [dirEq] using later.headChecked
     have localEffect : Matches later.middle later.actor (.push 139 (.stay 140)) := by simpa only [head] using later.headEffect
     have clamp := Upper190ResetState11.guarded141_before logged completed first sourceEq directionEq effect cheap
     have initialMate : ∃ box : Cell, box∈([141,140] : List Cell) ∧
         endGroup [141] (first.beforeOutcomes++[first.headOutcome])=[box] := by
       rcases clamp with normal|shifted
       · refine ⟨141,by simp,?_⟩
         rw [endGroup_append,normal,headEq]
         rfl
       · refine ⟨140,by simp,?_⟩
         rw [endGroup_append,shifted,headEq]
         rfl
     obtain ⟨box,member,tag⟩ := initialMate
     have stateMate := toState.end_subset (by decide) [141] (by decide) (by decide)
     have boxPresent : box∈first.actor.state.boulders := stateMate.2 (by rw [tag]; simp)
     have sourcePresent : 139∈first.actor.state.boulders := smallInside (shapeSmall.mem_iff.mpr (by simp [originalGroup]))
     have inexpensive := localCheap 141 box (by decide) tag
     have localSurvives := GuardedExit11.survives StationaryGuards11.guards141
       (Owner1007.locked_of_check _ [140,141] (by decide +kernel)) (by decide)
       (show advance soko1_1.board 139 .east=some 140 by decide +kernel)
       later.before.logged valid sourcePresent boxPresent member still inexpensive checked localEffect later.after
     have allEffects' := allEffects
     rw [head] at allEffects'
     have wholeShape : outcomes=(first.beforeOutcomes++[first.headOutcome])++
         (later.beforeOutcomes++ .push 139 (.stay 140)::later.afterOutcomes) :=
       allEffects'.symm.trans (List.append_assoc _ _ _)
     have full : endGroup [139] outcomes≠[] := by
       rw [wholeShape,endGroup_append,tag139]
       exact localSurvives
     exact False.elim (full (UpperCheapConsumed11.singletons_gone logged completed cheap 139 (by decide)))
   · have still := stationary 191 (by simp) srcEq
     have checked : step soko1_1.board later.middle .east=some later.actor := by simpa only [dirEq] using later.headChecked
     have localEffect : Matches later.middle later.actor (.push 191 (.stay 192)) := by simpa only [head] using later.headEffect
     have clamp := UpperResetGuards11.before193_reset logged completed first sourceEq directionEq effect cheap
     have initialMate : ∃ box : Cell, box∈([193,192] : List Cell) ∧
         endGroup [193] (first.beforeOutcomes++[first.headOutcome])=[box] := by
       rcases clamp with normal|shifted
       · refine ⟨193,by simp,?_⟩
         rw [endGroup_append,normal,headEq]
         rfl
       · refine ⟨192,by simp,?_⟩
         rw [endGroup_append,shifted,headEq]
         rfl
     obtain ⟨box,member,tag⟩ := initialMate
     have stateMate := toState.end_subset (by decide) [193] (by decide) (by decide)
     have boxPresent : box∈first.actor.state.boulders := stateMate.2 (by rw [tag]; simp)
     have sourcePresent : 191∈first.actor.state.boulders := smallInside (shapeSmall.mem_iff.mpr (by simp [originalGroup]))
     have inexpensive := localCheap 193 box (by decide) tag
     have localSurvives := GuardedExit11.survives StationaryGuards11.guards193
       (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) (by decide)
       (show advance soko1_1.board 191 .east=some 192 by decide +kernel)
       later.before.logged valid sourcePresent boxPresent member still inexpensive checked localEffect later.after
     have allEffects' := allEffects
     rw [head] at allEffects'
     have wholeShape : outcomes=(first.beforeOutcomes++[first.headOutcome])++
         (later.beforeOutcomes++ .push 191 (.stay 192)::later.afterOutcomes) :=
       allEffects'.symm.trans (List.append_assoc _ _ _)
     have full : endGroup [191] outcomes≠[] := by
       rw [wholeShape,endGroup_append,tag191]
       exact localSurvives
     exact False.elim (full (UpperCheapConsumed11.singletons_gone logged completed cheap 191 (by decide)))
   · have reset := UpperLocalAfter11.after_reset later reached smallUnique smallInside smallBound goodStart 138 srcEq
       (by simp [UpperReset11.Reset,dirEq])
     exact False.elim (excludeReset reset)
   · have reset := UpperLocalAfter11.after_reset later reached smallUnique smallInside smallBound goodStart 138 srcEq
       (by simp [UpperReset11.Reset,dirEq])
     exact False.elim (excludeReset reset)
   · have reset := UpperLocalAfter11.after_reset later reached smallUnique smallInside smallBound goodStart 190 srcEq
       (by simp [UpperReset11.Reset,dirEq])
     exact False.elim (excludeReset reset)
   · have localStill := UpperLocal19011.stationary_before_west later reached smallUnique smallInside smallBound goodStart srcEq dirEq
     have whole137 : ownPushes [137] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)=0 := by
       rw [ownPushes_append,tag137,state137,localStill.1]
     have whole139 : ownPushes [139] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)=0 := by
       rw [ownPushes_append,tag139,state139,localStill.2]
     obtain ⟨source,owner,metadata,_⟩ := later.headPaid
     have same : source=190 := Option.some.inj (metadata.symm.trans srcEq)
     have inSmall : 190∈endGroup small later.beforeOutcomes := same ▸ owner
     have inOriginal : 190∈endGroup originalGroup ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes) := by
       rw [endGroup_append,startSmall]
       exact inSmall
     have currentTag := Upper190Identity11.original191_at190 toCurrent whole137 whole139 inOriginal
     have cheap188 := UpperResetBudget11.cheap_c_two logged completed first 1 sourceEq directionEq effect cheap 188 (by decide)
     have prefixBound := prefix_energy_le toCurrent (Logged.cons later.headChecked later.headEffect later.after) [188] (by decide) (by decide)
     rw [allEffects] at prefixBound
     have prefixCheap : energy soko1_1.initial later.middle [188] ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)<2 := by omega
     have checked : step soko1_1.board later.middle .west=some later.actor := by simpa only [dirEq] using later.headChecked
     have localEffect : Matches later.middle later.actor (.push 190 (.stay 189)) := by simpa only [head] using later.headEffect
     rcases Upper190Parked11.after_west toCurrent checked localEffect later.after whole137 whole139 currentTag prefixCheap with survives|good
     · have allEffects' := allEffects
       rw [head] at allEffects'
       have full : endGroup [191] outcomes≠[] := by rw [←allEffects']; exact survives
       exact False.elim (full (UpperCheapConsumed11.singletons_gone logged completed cheap 191 (by decide)))
     · rw [←head] at good
       have beforePark := toCurrent.end_subset (by decide) Upper190Parked11.group (by decide) (by decide)
       have nextUnique := GhostSubset.update_unique _ _ _ later.headEffect currentActual _ beforePark.1 beforePark.2
       have nextInside := GhostSubset.update_subset _ _ _ later.headEffect _ beforePark.1 beforePark.2
       have size := endGroup_length_le Upper190Parked11.group ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)
       have nextBound := Nat.le_trans (update_length _ later.headOutcome) size
       have beforeInclude := end_subset_selected toCurrent (by decide) Upper190Parked11.group U6 (by decide) (by decide) (by decide) (by decide)
       have afterInclude := update_mono _ _ beforePark.1 beforeInclude later.headOutcome
       have bigCurrent : endGroup U6 ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)=endGroup big later.beforeOutcomes := by
         rw [endGroup_append,startBig]
       rw [bigCurrent] at afterInclude
       have price := ParkedEnergy11.future_energy nextReached later.after completed
         (update (endGroup Upper190Parked11.group ((first.beforeOutcomes++[first.headOutcome])++later.beforeOutcomes)) later.headOutcome)
         nextUnique nextInside nextBound good
       have less := cap _ nextUnique afterInclude
       omega
   · have localEffect : Matches later.middle later.actor (.push 216 (.stay 217)) := by simpa only [head] using later.headEffect
     obtain ⟨pair,good⟩ := UpperLocalAfter11.after216 later reached smallUnique smallInside smallBound goodStart srcEq localEffect
     have inside : [191,217]⊆later.actor.state.boulders := List.Subset.trans pair nextSmallInside
     have subset : [191,217]⊆UpperLocalBudget11.next later big := List.Subset.trans pair nextInclude
     have consumed := goneSmall [191,217] (by decide) subset
     have price := UpperConsumedFuture11.future_two (limit:=2) (PostEnergy11.closed true) (PostEnergy11.unique true)
       (by decide +kernel) (PostEnergy11.is_exit true) nextReached later.after [191,217] (by decide) inside (by decide) good consumed
     have less := cap [191,217] (by decide) subset
     omega
#print axioms upper_six
end Owner1007.Upper190EastSix11
