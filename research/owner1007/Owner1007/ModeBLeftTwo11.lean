import Owner1007.AfterForwardLeftTwo11
import Owner1007.LeftTwoLaneCanonical11
import Owner1007.RightEarlyWest11
import Owner1007.ForwardPrices11
import Owner1007.Left186TagPrice11
import Owner1007.ModeLeftSix32711
import Owner1007.Budget327OnlyB11
namespace Owner1007.ModeBLeftTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327)
 (capUpper : energy soko1_1.initial final UpperBudget11.U6 outcomes≤6)
 (capRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (capLeft : energy soko1_1.initial final [186] outcomes≤2) : False := by
 obtain ⟨forward,source190,west,head190,tag191,zero137,zero139⟩:=RightEarlyWest11.first_west logged completed (by omega) capRest
 obtain ⟨tag186,tag188⟩:=LeftTwoLaneCanonical11.at_forward forward completed cheap capLeft (by omega) capRest source190 west head190 tag191
 have checked : step soko1_1.board forward.middle .west=some forward.actor := by simpa only [west] using forward.headChecked
 have effect : Matches forward.middle forward.actor (.push 190 (.stay 189)) := by simpa only [head190] using forward.headEffect
 let headLogged : Logged soko1_1.board forward.middle [.west] forward.actor.state forward.actor.pushCost 1 [.push 190 (.stay 189)] :=
  .cons checked effect (.nil _)
 let lead:=forward.before.logged.append headLogged
 have pairBefore:=ForwardSnapshots11.pair_perm forward.before.logged zero139 tag191
 have prefixPair:=ForwardPrices11.pair_two forward.before.logged checked effect pairBefore
 have prefixUpper:=ForwardPrices11.upper_four forward.before.logged checked effect pairBefore tag188
 have after186 : endGroup [186] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[185] := by
  rw [endGroup_append,tag186]
  simp [endGroup,update,move]
 have after188 : endGroup [188] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[187] := by
  rw [endGroup_append,tag188]
  simp [endGroup,update,move]
 have after191 : endGroup [191] (forward.beforeOutcomes++[.push 190 (.stay 189)])=[189] := by
  rw [endGroup_append,tag191]
  simp [endGroup,update,move,post]
 have prefixLeft:=Left186TagPrice11.at185_two lead after186
 have after137 : ownPushes [137] (forward.beforeOutcomes++[.push 190 (.stay 189)])=0 := by
  rw [ownPushes_append,no_push_unchanged _ _ zero137]
  simp [ownPushes,ownPush,zero137]
 have after139 : ownPushes [139] (forward.beforeOutcomes++[.push 190 (.stay 189)])=0 := by
  rw [ownPushes_append,no_push_unchanged _ _ zero139]
  simp [ownPushes,ownPush,zero139]
 have player : forward.actor.state.player=190 := by rw [effect.2]
 have sequence : (forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes=outcomes := by
  have eq:=forward.outcomesEq
  rw [head190] at eq
  simpa only [List.append_assoc,List.singleton_append] using eq.symm
 have upper : energy soko1_1.initial final UpperBudget11.U6 ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)≤6 := by rw [sequence];exact capUpper
 have left : energy soko1_1.initial final [186] ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)≤2 := by rw [sequence];exact capLeft
 have rest : energy soko1_1.initial final UpperBudget11.Rest ((forward.beforeOutcomes++[.push 190 (.stay 189)])++forward.afterOutcomes)<2 := by rw [sequence];exact capRest
 have cost : forward.beforePushes+forward.actor.pushCost+forward.afterPushes≤327 := by have eq:=forward.pushesEq;omega
 exact AfterForwardLeftTwo11.impossible lead forward.after completed cost upper left rest prefixUpper prefixLeft prefixPair after186 after188 after191 after137 after139 player
#print axioms impossible
theorem only_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327) :
 energy soko1_1.initial final [186] outcomes=4∧energy soko1_1.initial final [212] outcomes=2 := by
 obtain ⟨_,upper,left,rest⟩:=Budget327OnlyB11.mode logged completed cheap
 rcases ModeLeftSix32711.left_split logged completed cheap upper left rest with bad|good
 ·have capUpper : energy soko1_1.initial final UpperBudget11.U6 outcomes≤6 := by omega
  have capRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2 := by omega
  exact False.elim (impossible logged completed cheap capUpper capRest (by omega))
 ·exact good
#print axioms only_four
end Owner1007.ModeBLeftTwo11
