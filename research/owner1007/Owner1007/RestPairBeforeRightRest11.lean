import Owner1007.RestBeforeRightRest11
import Owner1007.QuietGroupFixed11
import Owner1007.QuietFromCount11
import Owner1007.LoggedEventGap11
import Owner1007.CageFour12
namespace Owner1007.RestPairBeforeRightRest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ew {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source)
 (member : source∈([187,189]:List Cell)) : dir=.east∨dir=.west := by
 rcases step_cases_full _ _ _ _ checked with walked|pushed
 ·obtain ⟨target,_,_,_,_,shape⟩:=walked
  simp only [shape] at metadata
  contradiction
 ·obtain ⟨other,result,_,_,_,push,shape⟩:=pushed
  have same : other=source:=by simpa only [shape,Option.some.injEq] using metadata
  subst other
  have target:=(pushBoulder_spec _ _ _ _ _ push).2
  have all : ([187,189]:List Cell).all (fun source=>allDirs.all (fun dir=>decide (pushTargets soko1_1.board source dir=[]∨dir=.east∨dir=.west)))=true := by decide +kernel
  have row:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all source member) dir (Geometry.all_directions dir))
  rcases row with empty|east|west
  ·rw [empty] at target
   contradiction
  ·exact Or.inl east
  ·exact Or.inr west

theorem impossible
 {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes t lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (prefixLog : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (forwardHead : step soko1_1.board middle .west=some t) (forwardEffect : Matches middle t (.push 190 (.stay 189)))
 (lastLog : Logged soko1_1.board t.state lastDirs final lastPushes lastMoves last)
 (completed : Goal final)
 (upper : energy soko1_1.initial final UpperBudget11.U6 ((before++outcomes)++.push 190 (.stay 189)::last)≤8)
 (rest : energy soko1_1.initial final UpperBudget11.Rest ((before++outcomes)++.push 190 (.stay 189)::last)<2)
 (rightQuiet : UpperQuiet11.Quiet RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G
   (beforeDirs++dirs) middle (beforePushes+pushes) (beforeMoves+moves) (before++outcomes))
 (restOwner : 187∈endGroup UpperBudget11.Rest before)
 (physical : [187,189]⊆state.boulders) : False := by
 let finalTail:=Logged.cons forwardHead forwardEffect lastLog
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 rcases first_cut_or_quiet (paid:=fun _ _=>True) prefixLog [187,189] with found|quiet
 ·obtain ⟨cut⟩:=found
  have zero:=QuietGroupFixed11.whole_fixed cut.before (by intro c h d;trivial)
  have tag:=no_push_unchanged [187,189] cut.beforeOutcomes zero
  have pairFacts:=cut.before.logged.end_subset valid.1 [187,189] (by decide) physical
  have retained : [187,189]⊆endGroup [187,189] cut.beforeOutcomes:=by rw [tag];exact List.Subset.refl _
  have currentPhysical:=List.Subset.trans retained pairFacts.2
  let current:=first.append cut.before.logged
  let tail:=cut.after.append finalTail
  have currentValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant current.trace
  have dirEq : (beforeDirs++cut.beforeDirs)++cut.direction::cut.afterDirs=beforeDirs++dirs:=by
   calc
    _=beforeDirs++(cut.beforeDirs++cut.direction::cut.afterDirs):=by simp only [List.append_assoc]
    _=beforeDirs++dirs:=congrArg (fun rest=>beforeDirs++rest) cut.dirsEq.symm
  have outEq : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by
   calc
    _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc]
    _=before++outcomes:=congrArg (fun rest=>before++rest) cut.outcomesEq.symm
  have wholeCount:=FirstRest18711.quiet_count_zero rightQuiet
  have splitCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
      ((beforeDirs++cut.beforeDirs)++cut.direction::cut.afterDirs)
      ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)=0:=by rw [dirEq,outEq];exact wholeCount
  rw [PaidCount11.append current] at splitCount
  have beforeCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
      (beforeDirs++cut.beforeDirs) (before++cut.beforeOutcomes)=0:=by omega
  have rightBefore:=QuietFromCount11.from_count current RightEarlyWords11.G beforeCount
  obtain ⟨j,_,_,tag191,_,fixed137,fixed139⟩:=RightEarlyWords11.quiet_packet rightBefore
  have totalEq : (before++cut.beforeOutcomes)++cut.headOutcome::(cut.afterOutcomes++.push 190 (.stay 189)::last)=
      (before++outcomes)++.push 190 (.stay 189)::last:=by
   calc
    _=((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)++.push 190 (.stay 189)::last:=by simp only [List.append_assoc,List.cons_append]
    _=(before++outcomes)++.push 190 (.stay 189)::last:=congrArg (fun pre=>pre++.push 190 (.stay 189)::last) outEq
  have afterTotalEq : ((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++.push 190 (.stay 189)::last)=
      (before++outcomes)++.push 190 (.stay 189)::last:=by simpa only [List.append_assoc,List.singleton_append] using totalEq
  obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
  have member : source∈([187,189]:List Cell):=by rw [tag] at owner;exact owner
  have direction:=ew cut.headChecked metadata member
  have one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=
   .cons cut.headChecked cut.headEffect (.nil _)
  let nextFirst:=current.append one
  have afterFacts:=Upper216Eight11.next_facts cut first.trace (by decide) physical (by decide)
  have nextReached:=nextFirst.trace
  have dead {landing : Cell} (targets : pushTargets soko1_1.board source cut.direction=[landing])
   (unfilled : landing∉soko1_1.initial.holes) (frozen : List Cell) (locked : Locked soko1_1.board frozen)
   (shift : frozen⊆landing::([187,189]:List Cell).erase source)
   (unique : frozen.Nodup) (two : frozen.length=2)
   (away : ∀c,c∈frozen→c∉([314,315,316]:List Cell)) : False:=by
   have shape:=UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata targets unfilled current.trace.holes_sublist.subset
   have kept:=CageFour12.shifted_inside (by decide : ([187,189]:List Cell).Nodup) retained owner shift
   have selected : frozen⊆Upper216Eight11.next cut:=by simpa only [Upper216Eight11.next,shape] using kept
   have phys:=List.Subset.trans selected afterFacts.2.1
   exact Spare315Rest11.frozen_pair nextFirst tail completed (by change energy soko1_1.initial final UpperBudget11.Rest (((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++.push 190 (.stay 189)::last))<2;rw [afterTotalEq];exact rest) frozen locked unique two phys away
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·rcases direction with east|west
   ·exact dead (landing:=188) (by rw [east];decide +kernel) (by decide +kernel) [188,189]
      (locked_of_check _ [188,189] (by decide +kernel)) (by decide) (by decide) rfl (by decide)
   ·have fixed187:=cut.before.fixed (by decide :187∈([187,189]:List Cell)) (by intro d;trivial)
    have tag187:=no_push_unchanged [187] cut.beforeOutcomes fixed187
    have rootBefore:=first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
    have included:=end_subset_selected cut.before.logged valid.1 [187] (endGroup UpperBudget11.Rest before)
      (by decide) rootBefore.1 (by simpa using restOwner) rootBefore.2
    have localOwn : 187∈endGroup (endGroup UpperBudget11.Rest before) cut.beforeOutcomes:=included (by rw [tag187];simp)
    have owns : 187∈endGroup UpperBudget11.Rest (before++cut.beforeOutcomes):=by rw [endGroup_append];exact localOwn
    have restFacts:=current.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
    have row:=UpperLocalPrice11.exit_row currentValid restFacts.1 restFacts.2 cut.headChecked cut.headEffect
      ⟨187,owns,metadata,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources,west]⟩
    have gap:=logged_event_gap_le current cut.headChecked cut.headEffect tail UpperBudget11.Rest (by decide) (by decide)
    have bound:=Int.le_trans row gap
    change 2≤energy soko1_1.initial final UpperBudget11.Rest
      ((before++cut.beforeOutcomes)++cut.headOutcome::(cut.afterOutcomes++.push 190 (.stay 189)::last)) at bound
    rw [totalEq] at bound
    omega
  ·rcases direction with east|west
   ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 189 .east=[190] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 189 (.stay 190)):=by simpa only [headEq] using cut.headEffect
    have qcases : RightEarlyWords11.q j=191∨RightEarlyWords11.q j=190:=by unfold RightEarlyWords11.q;split <;>simp
    rcases qcases with q191|q190
    ·have present191 : 191∈cut.middle.boulders:=
      (current.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [tag191,q191];simp)
     have nextPhysical : [190,191]⊆cut.actor.state.boulders:=by
      rw [effect.2]
      intro c found
      rcases List.mem_cons.mp found with rfl|later
      ·exact List.mem_cons_self
      ·have same : c=191:=List.mem_singleton.mp later
       subst c
       exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :191≠189)).mpr present191)
     have fixedAfter137 : ownPushes [137] ((before++cut.beforeOutcomes)++[cut.headOutcome])=0:=by
      rw [ownPushes_append,no_push_unchanged _ _ fixed137,headEq]
      simpa [ownPushes,ownPush] using fixed137
     have fixedAfter139 : ownPushes [139] ((before++cut.beforeOutcomes)++[cut.headOutcome])=0:=by
      rw [ownPushes_append,no_push_unchanged _ _ fixed139,headEq]
      simpa [ownPushes,ownPush] using fixed139
     have hero : cut.actor.state.player∈Row19019111.region 0:=by rw [effect.2];exact Row19019111.hero189
     have nextUpper : energy soko1_1.initial final UpperBudget11.U6
       (((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++.push 190 (.stay 189)::last))≤8:=by rw [afterTotalEq];exact upper
     have nextRest : energy soko1_1.initial final UpperBudget11.Rest
       (((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++.push 190 (.stay 189)::last))<2:=by rw [afterTotalEq];omega
     exact Row190191Rest11.excluded nextFirst tail completed nextUpper nextRest fixedAfter137 fixedAfter139 nextPhysical hero
    ·have present190 : 190∈cut.middle.boulders:=
      (current.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [tag191,q190];simp)
     obtain ⟨result,_,push⟩:=effect_push_data checked effect
     obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
     have same : dest=190:=Option.some.inj (next.symm.trans (show advance soko1_1.board 189 .east=some 190 by decide +kernel))
     exact clear (same.symm ▸ present190)
   ·exact dead (landing:=188) (by rw [west];decide +kernel) (by decide +kernel) [187,188]
      (locked_of_check _ [187,188] (by decide +kernel)) (by decide) (by decide) rfl (by decide)
 ·have zero:=QuietGroupFixed11.whole_fixed quiet (by intro c h d;trivial)
  have tag:=no_push_unchanged [187,189] outcomes zero
  have present:=prefixLog.end_subset valid.1 [187,189] (by decide) physical
  have present189 : 189∈middle.boulders:=present.2 (by rw [tag];simp)
  obtain ⟨result,_,push⟩:=effect_push_data forwardHead forwardEffect
  obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
  have same : dest=189:=Option.some.inj (next.symm.trans (show advance soko1_1.board 190 .west=some 189 by decide +kernel))
  exact clear (same.symm ▸ present189)
#print axioms ew
#print axioms impossible
end Owner1007.RestPairBeforeRightRest11
