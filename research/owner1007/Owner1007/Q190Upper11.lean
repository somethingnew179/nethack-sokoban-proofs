import Owner1007.Q190Upper11Helpers
import Owner1007.QuietFixed11
import Owner1007.LoggedAppend11
namespace Owner1007.Q190Upper11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem future_four {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)≤4)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (i : Fin 3) (same : group.Perm (locks i)) (hero : state.player∈region i)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have bound4 : group.length≤4:=by have len:=same.length_eq;rw [size] at len;omega
 have bounded : group.length≤18:=by omega
 have good : OwnedCorral11.Good locks region state group:=⟨i,hero,fun _ h=>same.mem_iff.mpr h⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique nonempty logged valid.1 uniqueGroup inside good first.trace.holes_sublist.subset gone
 obtain ⟨j,heroBefore,locksBefore⟩:=Upper216Eight11.quiet_good_any closed unique cut.before valid.1 uniqueGroup inside good first.trace.holes_sublist.subset
 have beforeFirst:=first.append cut.before.logged
 have beforeValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant beforeFirst.trace
 have beforeFacts:=cut.before.logged.end_subset valid.1 group uniqueGroup inside
 have beforeBound : (endGroup group cut.beforeOutcomes).length≤4:=Nat.le_trans (endGroup_length_le _ _) bound4
 have afterFacts:=Upper216Eight11.next_facts cut first.trace uniqueGroup inside bounded
 have afterReached:=beforeFirst.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have afterGone:=Upper216Eight11.tail_gone cut gone
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by rw [List.append_assoc,←cut.outcomesEq]
 have stationarity : ∀c∈([137,139]:List Cell),ownPushes [c] (before++cut.beforeOutcomes)=0:=by
  intro c member
  have inLocks : c∈locks i:=by
   rcases (show c=137∨c=139 by simpa using member) with rfl|rfl <;> simp [locks]
  have localZero:=cut.before.fixed (same.mem_iff.mpr inLocks) (by
   intro d
   rcases (show c=137∨c=139 by simpa using member) with rfl|rfl <;> simp [paid])
  have initialZero : ownPushes [c] before=0:=by
   rcases (show c=137∨c=139 by simpa using member) with rfl|rfl
   ·exact zero137
   ·exact zero139
  rw [ownPushes_append,no_push_unchanged _ _ initialZero,initialZero,localZero]
 obtain ⟨source,owner,metadata,shape⟩:=head_shape j heroBefore locksBefore beforeFacts.2 beforeBound cut.headChecked cut.headPaid
 rcases shape with ⟨sources,west⟩|⟨rfl,directions⟩
 · have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have row:=UpperLocalPrice11.exit_row beforeValid beforeFacts.1 beforeFacts.2 cut.headChecked cut.headEffect
    ⟨source,owner,metadata,by rw [west];rcases sources with rfl|rfl <;> simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
   have sourceCase : source=187∨source=188:=sources
   have effectEq : cut.headOutcome=.push source (.stay (source-1)):=by
    rcases sourceCase with rfl|rfl
    ·exact UpperHeadCases11.ordinary_effect checked cut.headEffect metadata (by decide +kernel) (by decide +kernel) beforeFirst.trace.holes_sublist.subset
    ·exact UpperHeadCases11.ordinary_effect checked cut.headEffect metadata (by decide +kernel) (by decide +kernel) beforeFirst.trace.holes_sublist.subset
   have three : [137,139,190]⊆endGroup group cut.beforeOutcomes:=by
    apply List.Subset.trans (show [137,139,190]⊆locks j by simp [locks,List.subset_def]) locksBefore
   have lifted:=update_mono [137,139,190] (endGroup group cut.beforeOutcomes) (by decide) three cut.headOutcome
   have selected : UpperZero11.locks 12⊆Upper216Eight11.next cut:=by
    change _⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
    apply List.Subset.trans (l₂:=update [137,139,190] cut.headOutcome) _ lifted
    rw [effectEq]
    rcases sourceCase with rfl|rfl <;> decide +kernel
   have afterHero : cut.actor.state.player∈UpperZero11.region 12:=by
    have h : cut.actor.state.player=source:=by have ef:=cut.headEffect;rw [effectEq] at ef;rw [ef.2]
    rw [h]
    rcases sourceCase with rfl|rfl <;> decide +kernel
   have tailTwo:=zero_future_two afterReached cut.after completed (Upper216Eight11.next cut) afterFacts.1 afterFacts.2.1 afterFacts.2.2 12 selected afterHero
   exact cut_four cut first.trace uniqueGroup inside bounded row tailTwo
 · rcases directions with north|east|west
   · have checked : step soko1_1.board cut.middle .north=some cut.actor:=by simpa only [north] using cut.headChecked
     have effectEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 190 .north=[164] by decide +kernel) (by decide +kernel) beforeFirst.trace.holes_sublist.subset
     have effect : Matches cut.middle cut.actor (.push 190 (.stay 164)):=by simpa only [effectEq] using cut.headEffect
     have eq:=allEffects
     rw [effectEq] at eq
     have contradiction:=StrongShaftGate11.gate_moved_before_north beforeFirst checked effect cut.after completed
      (by rw [eq];exact upperCap) (by rw [eq];exact restCap)
     have z137:=stationarity 137 (by simp)
     have z139:=stationarity 139 (by simp)
     omega
   · have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
     have effectEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 190 .east=[191] by decide +kernel) (by decide +kernel) beforeFirst.trace.holes_sublist.subset
     have row:=UpperLocalPrice11.exit_row beforeValid beforeFacts.1 beforeFacts.2 cut.headChecked cut.headEffect
      ⟨190,owner,metadata,by rw [east];decide +kernel⟩
     have three : [137,139,190]⊆endGroup group cut.beforeOutcomes:=
      List.Subset.trans (show [137,139,190]⊆locks j by simp [locks,List.subset_def]) locksBefore
     have lifted:=update_mono [137,139,190] (endGroup group cut.beforeOutcomes) (by decide) three cut.headOutcome
     have selected : UpperZero11.locks 0⊆Upper216Eight11.next cut:=by
      change _⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
      apply List.Subset.trans (l₂:=update [137,139,190] cut.headOutcome) _ lifted
      rw [effectEq]
      decide +kernel
     have afterHero : cut.actor.state.player∈UpperZero11.region 0:=by
      have h : cut.actor.state.player=190:=by have ef:=cut.headEffect;rw [effectEq] at ef;rw [ef.2]
      rw [h];decide +kernel
     have tailTwo:=zero_future_two afterReached cut.after completed (Upper216Eight11.next cut) afterFacts.1 afterFacts.2.1 afterFacts.2.2 0 selected afterHero
     exact cut_four cut first.trace uniqueGroup inside bounded row tailTwo
   · have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
     have effectEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 190 .west=[189] by decide +kernel) (by decide +kernel) beforeFirst.trace.holes_sublist.subset
     have row:=UpperLocalPrice11.exit_row beforeValid beforeFacts.1 beforeFacts.2 cut.headChecked cut.headEffect
      ⟨190,owner,metadata,by rw [west];decide +kernel⟩
     obtain ⟨j,jBound⟩:=j
     have cases : j=0∨j=1∨j=2:=by omega
     rcases cases with rfl|rfl|rfl
     · have lifted:=update_mono (locks 0) (endGroup group cut.beforeOutcomes) (unique 0) locksBefore cut.headOutcome
       have selected : Upper187Cover11.locks 0⊆Upper216Eight11.next cut:=by
        change _⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
        apply List.Subset.trans (l₂:=update (locks 0) cut.headOutcome) _ lifted
        rw [effectEq];decide +kernel
       have afterHero : cut.actor.state.player∈Upper187Cover11.region 0:=by
        have h : cut.actor.state.player=190:=by have ef:=cut.headEffect;rw [effectEq] at ef;rw [ef.2]
        rw [h];decide +kernel
       have tailTwo:=Upper187Cover11.future_energy afterReached cut.after (Upper216Eight11.next cut) afterFacts.1 afterFacts.2.1 afterFacts.2.2 ⟨0,afterHero,selected⟩ afterGone
       exact cut_four cut first.trace uniqueGroup inside bounded row tailTwo
     · have lifted:=update_mono (locks 1) (endGroup group cut.beforeOutcomes) (unique 1) locksBefore cut.headOutcome
       have selected : [188,189]⊆Upper216Eight11.next cut:=by
        change _⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome
        apply List.Subset.trans (l₂:=update (locks 1) cut.headOutcome) _ lifted
        rw [effectEq];decide +kernel
       exact False.elim (Upper216Eight11.frozen_absurd cut.after
        (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1 afterFacts.1 afterFacts.2.1
        (locked_of_check _ [188,189] (by decide +kernel)) (List.Subset.trans selected afterFacts.2.1)
        (show 188∈[188,189] by decide) (selected (by decide)) afterGone)
     · have unblocked:=WestRankHead11.source_unblocked checked metadata (List.Subset.trans locksBefore beforeFacts.2)
       exact False.elim (unblocked (by change BlockedPush soko1_1.board (locks 2) 190 .west;decide +kernel))
#print axioms future_four
end Owner1007.Q190Upper11
