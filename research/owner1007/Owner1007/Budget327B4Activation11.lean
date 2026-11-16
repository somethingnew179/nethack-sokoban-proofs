import Owner1007.Budget327Forward18411
import Owner1007.RightParked21211
import Owner1007.RightParkedReady11
import Owner1007.TaggedSix11
import Owner1007.ForwardPrices11
import Owner1007.ForwardSnapshots11
namespace Owner1007.Budget327B4Activation11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11 Owner1007.RightParkedReady11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Each of four manually prescribed frames is impossible in its actual original history. -/
def Reserve : Prop := ∀ {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes},
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before) →
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) →
 ∀ i : Fin 4,Ready first last i→False

theorem impossible (reserve : Reserve) {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) : False := by
 obtain ⟨_,upper,left,rest⟩:=Budget327OnlyB11.mode logged completed cheap
 obtain ⟨left186,left212⟩:=ModeBLeftTwo11.only_four logged completed cheap
 obtain ⟨cut,metadata,west,head190,tag191,tag186,parkedChoice,zero137,zero139,noRest⟩:=
  Budget327Forward18411.first_packet logged completed cheap
 obtain ⟨parked,parkedCases,tag188⟩ : ∃parked,(parked=186∨parked=187)∧endGroup [188] cut.beforeOutcomes=[parked] := by
  rcases parkedChoice with h|h
  ·exact ⟨186,Or.inl rfl,h⟩
  ·exact ⟨187,Or.inr rfl,h⟩
 have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
 have effect : Matches cut.middle cut.actor (.push 190 (.stay 189)):=by simpa only [head190] using cut.headEffect
 let one : Logged soko1_1.board cut.middle [.west] cut.actor.state cut.actor.pushCost 1 [.push 190 (.stay 189)]:=
  .cons checked effect (.nil _)
 let first:=cut.before.logged.append one
 have pairBefore:=ForwardSnapshots11.pair_perm cut.before.logged zero139 tag191
 have prefixPair:=ForwardPrices11.pair_two cut.before.logged checked effect pairBefore
 have after186 : endGroup [186] (cut.beforeOutcomes++[.push 190 (.stay 189)])=[184]:=by
  rw [endGroup_append,tag186]
  simp [endGroup,update,move]
 have after188 : endGroup [188] (cut.beforeOutcomes++[.push 190 (.stay 189)])=[parked]:=by
  rw [endGroup_append,tag188]
  rcases parkedCases with rfl|rfl <;>simp [endGroup,update,move]
 have after191 : endGroup [191] (cut.beforeOutcomes++[.push 190 (.stay 189)])=[189]:=by
  rw [endGroup_append,tag191]
  simp [endGroup,update,move,post]
 have prefixUpper : 4≤energy soko1_1.initial cut.actor.state UpperBudget11.U6 (cut.beforeOutcomes++[.push 190 (.stay 189)]) := by
  rcases parkedCases with h|h
  ·have six:=Upper188At18611.upper_six first (by simpa only[h] using after188) prefixPair
   omega
  ·exact ForwardPrices11.upper_four cut.before.logged checked effect pairBefore (by simpa only[h] using tag188)
 have after137 : ownPushes [137] (cut.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ zero137]
  simp [ownPushes,ownPush,zero137]
 have after139 : ownPushes [139] (cut.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ zero139]
  simp [ownPushes,ownPush,zero139]
 have afterNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
     (cut.beforeDirs++[.west]) (cut.beforeOutcomes++[.push 190 (.stay 189)])=0:=by
  rw [PaidCount11.append cut.before.logged]
  simp [PaidCount11.count,PaidCount11.owned,FirstRest18711.paid,noRest]
 have totalEq : (cut.beforeOutcomes++[.push 190 (.stay 189)])++cut.afterOutcomes=outcomes:=by
  have eq:=cut.outcomesEq
  rw [head190] at eq
  simpa only [List.append_assoc,List.singleton_append] using eq.symm
 have afterUpper : energy soko1_1.initial final UpperBudget11.U6
     ((cut.beforeOutcomes++[.push 190 (.stay 189)])++cut.afterOutcomes)≤6:=by rw [totalEq];omega
 have afterLeft186 : energy soko1_1.initial final [186]
     ((cut.beforeOutcomes++[.push 190 (.stay 189)])++cut.afterOutcomes)≤4:=by rw [totalEq];omega
 have afterLeft212 : energy soko1_1.initial final [212]
     ((cut.beforeOutcomes++[.push 190 (.stay 189)])++cut.afterOutcomes)≤2:=by rw [totalEq];omega
 have afterRest : energy soko1_1.initial final UpperBudget11.Rest
     ((cut.beforeOutcomes++[.push 190 (.stay 189)])++cut.afterOutcomes)<2:=by rw [totalEq];omega
 have afterCheap : cut.beforePushes+cut.actor.pushCost+cut.afterPushes≤327:=by
  have counts:=cut.pushesEq
  omega
 have player : cut.actor.state.player=190:=matches_hero cut.middle cut.actor (.push 190 (.stay 189)) effect
 obtain ⟨cell,cellCases,after212,_⟩:=RightParked21211.two_cells first cut.after completed (by omega)
  afterUpper afterLeft186 afterLeft212 afterRest afterNoRest parked parkedCases after186 after188 after191 player
 obtain ⟨i,parkedEq,cellEq⟩ : ∃i : Fin 4,u i=parked∧marker i=cell := by
  rcases parkedCases with rfl|rfl <;>rcases cellCases with rfl|rfl
  ·exact ⟨1,rfl,rfl⟩
  ·exact ⟨3,rfl,rfl⟩
  ·exact ⟨0,rfl,rfl⟩
  ·exact ⟨2,rfl,rfl⟩
 obtain ⟨unique,physical,gone,_⟩:=TaggedSix11.owned first cut.after completed afterUpper afterLeft186 afterLeft212
  after137 after139 184 cell parked 189 after186 after212 after188 after191
 have perm : ([137,139,184,cell,parked,189]:List Cell).Perm [137,139,184,parked,189,cell] :=
  List.Perm.cons 137 (List.Perm.cons 139 (List.Perm.cons 184 (show ([cell]++[parked,189]).Perm ([parked,189]++[cell]) from List.perm_append_comm)))
 have physicalFrame : locks i⊆cut.actor.state.boulders := by
  change [137,139,184,u i,189,marker i]⊆cut.actor.state.boulders
  rw [parkedEq,cellEq]
  exact fun x h=>physical (perm.mem_iff.mpr h)
 have goneFrame : endGroup (locks i) cut.afterOutcomes=[] := by
  have same:=endGroup_perm perm cut.afterOutcomes
  rw [gone] at same
  change endGroup [137,139,184,u i,189,marker i] cut.afterOutcomes=[]
  rw [parkedEq,cellEq]
  exact List.perm_nil.mp same.symm
 have ready : Ready first cut.after i := {
  completed:=completed,cheap:=afterCheap,upper:=afterUpper,left186:=afterLeft186,left212:=afterLeft212,
  rest:=afterRest,noRest:=afterNoRest,zero137:=after137,zero139:=after139,tag186:=after186,
  tag188:=by rw [parkedEq];exact after188,
  tag191:=after191,tag212:=by rw [cellEq];exact after212,
  pairTwo:=prefixPair,upperFour:=prefixUpper,physical:=physicalFrame,
  hero:=by rw [player];exact (show ∀j : Fin 4,(190:Cell)∈region j from by decide +kernel) i,
  gone:=goneFrame }
 exact reserve first cut.after i ready
#print axioms impossible
end Owner1007.Budget327B4Activation11
