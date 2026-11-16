import Owner1007.RightEarlyWest11
import Owner1007.Earlier188East32711
import Owner1007.Row19019132711
import Owner1007.QuietFromCount11
namespace Owner1007.Zero186Cycle32711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (upperCheap : energy soko1_1.initial final U6 outcomes<8)
 (restCheap : energy soko1_1.initial final Rest outcomes<2)
 (zero186 : energy soko1_1.initial final [186] outcomes=0) : False:=by
 obtain ⟨forward,source190,west,head190,tag191,_,_⟩:=RightEarlyWest11.first_west logged completed upperCheap restCheap
 have forwardChecked : step soko1_1.board forward.middle .west=some forward.actor:=by
   simpa only [west] using forward.headChecked
 have forwardEffect : Matches forward.middle forward.actor (.push 190 (.stay 189)):=by
   simpa only [head190] using forward.headEffect
 have forwardCheap : forward.beforePushes+forward.actor.pushCost+forward.afterPushes≤327:=by
   have counts:=forward.pushesEq
   omega
 have sequence:=forward.outcomesEq
 rw [head190] at sequence
 have zeroForward : energy soko1_1.initial final [186]
     (forward.beforeOutcomes++.push 190 (.stay 189)::forward.afterOutcomes)=0:=by
   rw [←sequence]
   exact zero186
 obtain ⟨early⟩:=Earlier188East32711.before_west190 forward.before.logged forwardChecked forwardEffect
   forward.after completed forwardCheap zeroForward
 obtain ⟨source189,east,head189⟩:=Earlier188East32711.head_shape early
 have earlyChecked : step soko1_1.board early.middle .east=some early.actor:=by
   simpa only [east] using early.headChecked
 have earlyEffect : Matches early.middle early.actor (.push 189 (.stay 190)):=by
   simpa only [head189] using early.headEffect
 have wholeCount:=FirstRest18711.quiet_count_zero forward.before
 have concatZero : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
     (early.beforeDirs++early.direction::early.afterDirs)
     (early.beforeOutcomes++early.headOutcome::early.afterOutcomes)=0:=by
   rw [←early.dirsEq,←early.outcomesEq]
   exact wholeCount
 have appendCount:=PaidCount11.append early.before.logged RightEarlyWords11.paid RightEarlyWords11.G
   (early.direction::early.afterDirs) (early.headOutcome::early.afterOutcomes)
 rw [appendCount] at concatZero
 have beforeCount : PaidCount11.count RightEarlyWords11.paid RightEarlyWords11.G
     early.beforeDirs early.beforeOutcomes=0:=by omega
 have prefixQuiet:=QuietFromCount11.from_count early.before.logged RightEarlyWords11.G beforeCount
 obtain ⟨i,_,_,before191,_,zero137,zero139⟩:=RightEarlyWords11.quiet_packet prefixQuiet
 have qCases : RightEarlyWords11.q i=191∨RightEarlyWords11.q i=190:=by
   unfold RightEarlyWords11.q
   split <;> simp
 rcases qCases with is191|is190
 ·rw [is191] at before191
  have present191 : 191∈early.middle.boulders:=
    (early.before.logged.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [before191];simp)
  have physical : [190,191]⊆early.actor.state.boulders:=by
    rw [earlyEffect.2]
    intro c h
    rcases List.mem_cons.mp h with rfl|later
    ·exact List.mem_cons_self
    ·have same : c=191:=List.mem_singleton.mp later
     subst c
     exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :191≠189)).mpr present191)
  let one : Logged soko1_1.board early.middle [.east] early.actor.state early.actor.pushCost 1 [.push 189 (.stay 190)]:=
    .cons earlyChecked earlyEffect (.nil _)
  let first:=early.before.logged.append one
  let suffix:=early.after.append (Logged.cons forward.headChecked forward.headEffect forward.after)
  have totalCheap : early.beforePushes+early.actor.pushCost+
      (early.afterPushes+(forward.actor.pushCost+forward.afterPushes))≤327:=by
    have earlyCounts:=early.pushesEq
    have forwardCounts:=forward.pushesEq
    omega
  have after137 : ownPushes [137] (early.beforeOutcomes++[.push 189 (.stay 190)])=0:=by
    rw [ownPushes_append,no_push_unchanged _ _ zero137]
    simpa [ownPushes,ownPush] using zero137
  have after139 : ownPushes [139] (early.beforeOutcomes++[.push 189 (.stay 190)])=0:=by
    rw [ownPushes_append,no_push_unchanged _ _ zero139]
    simpa [ownPushes,ownPush] using zero139
  have hero : early.actor.state.player∈Row19019111.region 0:=by
    have same : early.actor.state.player=189:=by rw [earlyEffect.2]
    rw [same]
    exact Row19019111.hero189
  have allEffects : (early.beforeOutcomes++[.push 189 (.stay 190)])++
      (early.afterOutcomes++forward.headOutcome::forward.afterOutcomes)=outcomes := by
   calc
    _=(early.beforeOutcomes++early.headOutcome::early.afterOutcomes)++forward.headOutcome::forward.afterOutcomes := by rw [head189];simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
    _=forward.beforeOutcomes++forward.headOutcome::forward.afterOutcomes :=
      congrArg (fun before=>before++forward.headOutcome::forward.afterOutcomes) early.outcomesEq.symm
    _=outcomes := forward.outcomesEq.symm
  have upperEvent : energy soko1_1.initial final U6
      ((early.beforeOutcomes++[.push 189 (.stay 190)])++(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes))<8 := by rw [allEffects];exact upperCheap
  have restEvent : energy soko1_1.initial final Rest
      ((early.beforeOutcomes++[.push 189 (.stay 190)])++(early.afterOutcomes++forward.headOutcome::forward.afterOutcomes))<2 := by rw [allEffects];exact restCheap
  exact Row19019132711.excluded first suffix completed totalCheap upperEvent restEvent after137 after139 physical hero
 ·rw [is190] at before191
  have present190 : 190∈early.middle.boulders:=
    (early.before.logged.end_subset (by decide) [191] (by decide) (by decide)).2 (by rw [before191];simp)
  obtain ⟨result,_,push⟩:=effect_push_data earlyChecked earlyEffect
  obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
  have destEq : dest=190:=Option.some.inj (next.symm.trans (show advance soko1_1.board 189 .east=some 190 by decide +kernel))
  exact clear (destEq.symm ▸ present190)
#print axioms impossible
end Owner1007.Zero186Cycle32711

