import Owner1007.RestPairBeforeRight11
import Owner1007.RightEarlyStrong11
namespace Owner1007.RestAfterForward11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_north_before {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327)
 (left : energy soko1_1.initial final [186] outcomes≤4)
 (upper : energy soko1_1.initial final UpperBudget11.U6 outcomes<8)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (forward : FirstCut RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs final pushes moves outcomes)
 (source190 : forward.actor.pushSource=some 190) (west : forward.direction=.west)
 (head190 : forward.headOutcome=.push 190 (.stay 189)) :
 PaidCount11.count FirstRest18711.paid UpperBudget11.Rest forward.beforeDirs forward.beforeOutcomes=0 := by
 have checkedForward : step soko1_1.board forward.middle .west=some forward.actor:=by simpa only [west] using forward.headChecked
 have effectForward : Matches forward.middle forward.actor (.push 190 (.stay 189)):=by simpa only [head190] using forward.headEffect
 rcases first_cut_or_quiet (paid:=FirstRest18711.paid) forward.before.logged UpperBudget11.Rest with found|quiet
 ·obtain ⟨early⟩:=found
  have shape:=FirstRest18711.head_shape early
  have checked : step soko1_1.board early.middle .north=some early.actor:=by simpa only [shape.2.1] using early.headChecked
  have effect : Matches early.middle early.actor (.push 213 (.stay 187)):=by simpa only [shape.2.2] using early.headEffect
  have wholeCount:=FirstRest18711.quiet_count_zero forward.before
  have concatCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
      (early.beforeDirs++early.direction::early.afterDirs) (early.beforeOutcomes++early.headOutcome::early.afterOutcomes)=0:=by
   rw [←early.dirsEq,←early.outcomesEq]
   exact wholeCount
  rw [PaidCount11.append early.before.logged] at concatCount
  have beforeCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G early.beforeDirs early.beforeOutcomes=0:=by omega
  have rightBefore:=QuietFromCount11.from_count early.before.logged RightEarlyWords11.G beforeCount
  let finalTail:=Logged.cons forward.headChecked forward.headEffect forward.after
  let suffix:=early.after.append finalTail
  have countsForward:=forward.pushesEq
  have countsEarly:=early.pushesEq
  have cheapEarly : early.beforePushes+early.actor.pushCost+(early.afterPushes+(forward.actor.pushCost+forward.afterPushes))≤327:=by omega
  have totalEq : early.beforeOutcomes++early.headOutcome::(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes)=outcomes:=by
   calc
    _=(early.beforeOutcomes++early.headOutcome::early.afterOutcomes)++forward.headOutcome::forward.afterOutcomes:=by simp only [List.append_assoc,List.cons_append]
    _=forward.beforeOutcomes++forward.headOutcome::forward.afterOutcomes:=congrArg (fun pre=>pre++forward.headOutcome::forward.afterOutcomes) early.outcomesEq.symm
    _=outcomes:=forward.outcomesEq.symm
  have earlyLeft : energy soko1_1.initial final [186]
      (early.beforeOutcomes++.push 213 (.stay 187)::(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes))≤4:=by
   rw [←shape.2.2,totalEq];exact left
  have earlyUpper : energy soko1_1.initial final UpperBudget11.U6
      (early.beforeOutcomes++.push 213 (.stay 187)::(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes))<8:=by
   rw [←shape.2.2,totalEq];exact upper
  have earlyRest : energy soko1_1.initial final UpperBudget11.Rest
      (early.beforeOutcomes++.push 213 (.stay 187)::(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes))<2:=by
   rw [←shape.2.2,totalEq];exact rest
  have tag188:=RestBeforeRightRow11.upper188_at189 rightBefore checked effect suffix completed cheapEarly earlyLeft earlyUpper earlyRest
  let one : Logged soko1_1.board early.middle [early.direction] early.actor.state early.actor.pushCost 1 [early.headOutcome]:=
   .cons early.headChecked early.headEffect (.nil _)
  let first:=early.before.logged.append one
  have physical : [187,189]⊆early.actor.state.boulders:=by
   have present189 : 189∈early.middle.boulders:=
     (early.before.logged.end_subset (by decide) [188] (by decide) (by decide)).2 (by rw [tag188];simp)
   rw [effect.2]
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   ·exact List.mem_cons_self
   ·have same : c=189:=List.mem_singleton.mp later
    subst c;exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :189≠213)).mpr present189)
  obtain ⟨source,owner,metadata,pays⟩:=early.headPaid
  rcases pays with ⟨rfl,north⟩
  have rootOwner : 187∈endGroup UpperBudget11.Rest (early.beforeOutcomes++[early.headOutcome]):=by
   rw [endGroup_append]
   change 187∈update (endGroup UpperBudget11.Rest early.beforeOutcomes) early.headOutcome
   rw [shape.2.2]
   simp only [update,move,if_pos owner,post]
   simp
  let joined:=first.append early.after
  have prefixDirEq : (early.beforeDirs++[early.direction])++early.afterDirs=forward.beforeDirs:=by
   simpa only [List.append_assoc,List.singleton_append] using early.dirsEq.symm
  have prefixOutEq : (early.beforeOutcomes++[early.headOutcome])++early.afterOutcomes=forward.beforeOutcomes:=by
   simpa only [List.append_assoc,List.singleton_append] using early.outcomesEq.symm
  have joinedCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
      ((early.beforeDirs++[early.direction])++early.afterDirs)
      ((early.beforeOutcomes++[early.headOutcome])++early.afterOutcomes)=0:=by rw [prefixDirEq,prefixOutEq];exact wholeCount
  have rightJoined:=QuietFromCount11.from_count joined RightEarlyWords11.G joinedCount
  have totalPair : (((early.beforeOutcomes++[early.headOutcome])++early.afterOutcomes)++.push 190 (.stay 189)::forward.afterOutcomes)=outcomes:=by
   rw [prefixOutEq,←head190]
   exact forward.outcomesEq.symm
  have upperPair : energy soko1_1.initial final UpperBudget11.U6
      (((early.beforeOutcomes++[early.headOutcome])++early.afterOutcomes)++.push 190 (.stay 189)::forward.afterOutcomes)≤8:=by rw [totalPair];omega
  have restPair : energy soko1_1.initial final UpperBudget11.Rest
      (((early.beforeOutcomes++[early.headOutcome])++early.afterOutcomes)++.push 190 (.stay 189)::forward.afterOutcomes)<2:=by rw [totalPair];exact rest
  have contradiction:=RestPairBeforeRight11.impossible first early.after checkedForward effectForward forward.after completed
    (by omega) upperPair restPair rightJoined rootOwner physical
  exact False.elim contradiction
 ·exact FirstRest18711.quiet_count_zero quiet
#print axioms no_north_before
end Owner1007.RestAfterForward11
