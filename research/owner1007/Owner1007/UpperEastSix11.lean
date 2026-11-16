import Owner1007.UpperSixExit11
namespace Owner1007.UpperEastSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11

theorem reserve139_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (directionEq : cut.direction=.east) (sourceEq : cut.actor.pushSource=some 139)
 (headEq : cut.headOutcome=.push 139 (.stay 140)) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have stationary := cut.stationary_source 139 (by decide) sourceEq
   have prefixCheap := UpperSixBudget11.prefix_four logged completed cut cheap 141 (by decide)
   have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [headEq] using cut.headEffect
   have survives := StationaryExitSix11.survives139 cut.before.logged checked effect cut.after stationary (by omega)
   have shape : outcomes=cut.beforeOutcomes ++ .push 139 (.stay 140)::cut.afterOutcomes := by
     simpa only [headEq] using cut.outcomesEq
   have original : endGroup [139] outcomes≠[] := by rw [shape]; exact survives
   exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 139 (by decide) original)
#print axioms reserve139_six

theorem reserve191_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (directionEq : cut.direction=.east) (sourceEq : cut.actor.pushSource=some 191)
 (headEq : cut.headOutcome=.push 191 (.stay 192)) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have stationary := cut.stationary_source 191 (by decide) sourceEq
   have prefixCheap := UpperSixBudget11.prefix_four logged completed cut cheap 193 (by decide)
   have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
   have effect : Matches cut.middle cut.actor (.push 191 (.stay 192)) := by simpa only [headEq] using cut.headEffect
   have survives := StationaryExitSix11.survives191 cut.before.logged checked effect cut.after stationary (by omega)
   have shape : outcomes=cut.beforeOutcomes ++ .push 191 (.stay 192)::cut.afterOutcomes := by
     simpa only [headEq] using cut.outcomesEq
   have original : endGroup [191] outcomes≠[] := by rw [shape]; exact survives
   exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 191 (by decide) original)
#print axioms reserve191_six
end Owner1007.UpperEastSix11
