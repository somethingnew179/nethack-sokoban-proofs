import Owner1007.Forward185187Excluded11
import Owner1007.RestAfterForward11
import Owner1007.ForwardPrices11
import Owner1007.ForwardSnapshots11
namespace Owner1007.Forward185187Excluded11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem at_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327)
 (upper : energy soko1_1.initial final UpperBudget11.U6 outcomes≤6)
 (left186 : energy soko1_1.initial final [186] outcomes≤4)
 (left212 : energy soko1_1.initial final [212] outcomes≤2)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (forward : FirstCut RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs final pushes moves outcomes)
 (source190 : forward.actor.pushSource=some 190) (west : forward.direction=.west)
 (head190 : forward.headOutcome=.push 190 (.stay 189))
 (tag191 : endGroup [191] forward.beforeOutcomes=[190])
 (tag186 : endGroup [186] forward.beforeOutcomes=[185])
 (tag188 : endGroup [188] forward.beforeOutcomes=[187]) : False := by
 obtain ⟨i,_,_,_,_,zero137,zero139⟩:=RightEarlyWords11.quiet_packet forward.before
 have noRestBefore:=RestAfterForward11.no_north_before logged completed cheap left186 (by omega) rest forward source190 west head190
 have checked : step soko1_1.board forward.middle .west=some forward.actor:=by simpa only [west] using forward.headChecked
 have effect : Matches forward.middle forward.actor (.push 190 (.stay 189)):=by simpa only [head190] using forward.headEffect
 let one : Logged soko1_1.board forward.middle [.west] forward.actor.state forward.actor.pushCost 1 [.push 190 (.stay 189)]:=
  .cons checked effect (.nil _)
 let first:=forward.before.logged.append one
 have pairBefore:=ForwardSnapshots11.pair_perm forward.before.logged zero139 tag191
 have prefixUpper:=ForwardPrices11.upper_four forward.before.logged checked effect pairBefore tag188
 have after186 : endGroup [186] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[185]:=by
  rw [endGroup_append,tag186]
  simp [endGroup,update,move]
 have after188 : endGroup [188] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[187]:=by
  rw [endGroup_append,tag188]
  simp [endGroup,update,move]
 have after191 : endGroup [191] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[189]:=by
  rw [endGroup_append,tag191]
  simp [endGroup,update,move,post]
 have after137 : ownPushes [137] (forward.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ zero137]
  simp [ownPushes,ownPush,zero137]
 have after139 : ownPushes [139] (forward.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ zero139]
  simp [ownPushes,ownPush,zero139]
 have afterNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
     (forward.beforeDirs++[.west]) (forward.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [PaidCount11.append forward.before.logged]
  simp [PaidCount11.count,PaidCount11.owned,FirstRest18711.paid,noRestBefore]
 have totalEq : (forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes=outcomes:=by
  have eq:=forward.outcomesEq
  rw [head190] at eq
  simpa only [List.append_assoc,List.singleton_append] using eq.symm
 have afterUpper : energy soko1_1.initial final UpperBudget11.U6
     ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)≤6:=by rw [totalEq];exact upper
 have afterLeft186 : energy soko1_1.initial final [186]
     ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)≤4:=by rw [totalEq];exact left186
 have afterLeft212 : energy soko1_1.initial final [212]
     ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)≤2:=by rw [totalEq];exact left212
 have afterRest : energy soko1_1.initial final UpperBudget11.Rest
     ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)<2:=by rw [totalEq];exact rest
 have afterCheap : forward.beforePushes+forward.actor.pushCost+forward.afterPushes<335:=by
  have counts:=forward.pushesEq
  omega
 exact impossible first forward.after completed afterCheap afterUpper afterLeft186 afterLeft212 afterRest
   afterNoRest after137 after139 prefixUpper after186 after188 after191
#print axioms at_first
end Owner1007.Forward185187Excluded11
