import Owner1007.Forward185187Excluded11AtFirst
import Owner1007.LeftFourLaneCanonical11
import Owner1007.ModeBLeftTwo11
import Owner1007.RightEarlyStrong11
namespace Owner1007.Budget327Forward18411
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A necessary original-trace restriction, not a327 winning witness. -/
theorem first_packet {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327) :
 ∃cut : FirstCut RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs final pushes moves outcomes,
 cut.actor.pushSource=some 190 ∧cut.direction=.west ∧cut.headOutcome=.push 190 (.stay 189) ∧
 endGroup [191] cut.beforeOutcomes=[190] ∧endGroup [186] cut.beforeOutcomes=[184] ∧
 (endGroup [188] cut.beforeOutcomes=[186]∨endGroup [188] cut.beforeOutcomes=[187]) ∧
 ownPushes [137] cut.beforeOutcomes=0 ∧ownPushes [139] cut.beforeOutcomes=0 ∧
 PaidCount11.count FirstRest18711.paid UpperBudget11.Rest cut.beforeDirs cut.beforeOutcomes=0 := by
 obtain ⟨_,upper,left,rest⟩:=Budget327OnlyB11.mode logged completed cheap
 obtain ⟨left186,left212⟩:=ModeBLeftTwo11.only_four logged completed cheap
 obtain ⟨cut,metadata,west,head,tag191,zero137,zero139⟩:=RightEarlyStrong11.first_west logged completed (by omega) (by omega)
 have noRest:=RestAfterForward11.no_north_before logged completed cheap (by omega) (by omega) (by omega) cut metadata west head
 rcases LeftFourLaneCanonical11.at_forward cut completed cheap (by omega) (by omega) (by omega) metadata west head tag191 with first|second|third
 ·exact ⟨cut,metadata,west,head,tag191,first.1,Or.inl first.2,zero137,zero139,noRest⟩
 ·exact ⟨cut,metadata,west,head,tag191,second.1,Or.inr second.2,zero137,zero139,noRest⟩
 ·exact False.elim (Forward185187Excluded11.at_first logged completed cheap (by omega) (by omega) (by omega) (by omega)
    cut metadata west head tag191 third.1 third.2)
#print axioms first_packet
end Owner1007.Budget327Forward18411
