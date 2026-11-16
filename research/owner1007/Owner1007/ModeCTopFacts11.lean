import Owner1007.ModeCTopSplit11
namespace Owner1007.ModeCTopFacts11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prefix_colored {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : pushes+lastPushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B (outcomes++last)≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)≤2)
 (noNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0) :
 endGroup Gate265Transport11.upperOrigins outcomes⊆Gate265Transport11.upper := by
 rcases ModeCTopSplit11.split prefixLog suffix completed cheap left rest noNorth
     Gate265Transport11.upperOrigins (by decide) (by decide) with quiet|afterBoundary
 ·exact Gate265Transport11.quiet_upper quiet
 ·obtain ⟨cut,zero⟩ := afterBoundary
  have tag := no_push_unchanged (endGroup Gate265Transport11.upperOrigins cut.beforeOutcomes)
    (cut.headOutcome::cut.afterOutcomes) zero
  rw [cut.outcomesEq,endGroup_append,tag]
  exact Gate265Transport11.quiet_upper cut.before

theorem prefix_down_zero {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : pushes+lastPushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B (outcomes++last)≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)≤2)
 (noNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0) :
 PaidCount11.count NoTopDown265Before18711.down Gate265Transport11.upperOrigins dirs outcomes=0 := by
 rcases ModeCTopSplit11.split prefixLog suffix completed cheap left rest noNorth
     Gate265Transport11.upperOrigins (by decide) (by decide) with quiet|afterBoundary
 ·exact NoTopDown265Before18711.quiet_count quiet
 ·obtain ⟨cut,zero⟩ := afterBoundary
  have before := NoTopDown265Before18711.quiet_count cut.before
  have bounded := TransportEvents11.count_le_ownPushes NoTopDown265Before18711.down
    (endGroup Gate265Transport11.upperOrigins cut.beforeOutcomes) (cut.direction::cut.afterDirs) (cut.headOutcome::cut.afterOutcomes)
  have tail : PaidCount11.count NoTopDown265Before18711.down
    (endGroup Gate265Transport11.upperOrigins cut.beforeOutcomes) (cut.direction::cut.afterDirs) (cut.headOutcome::cut.afterOutcomes)=0 := by omega
  have full : PaidCount11.count NoTopDown265Before18711.down Gate265Transport11.upperOrigins
    (cut.beforeDirs++cut.direction::cut.afterDirs) (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=0 := by
   rw [PaidCount11.append cut.before.logged,before,tail]
  simpa only [←cut.dirsEq,←cut.outcomesEq] using full

theorem before_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) :
 endGroup Gate265Transport11.upperOrigins cut.beforeOutcomes⊆Gate265Transport11.upper ∧
 PaidCount11.count NoTopDown265Before18711.down Gate265Transport11.upperOrigins cut.beforeDirs cut.beforeOutcomes=0 := by
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have counts:=cut.pushesEq
 have prefixCheap : cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤327 := by omega
 have leftCap : energy soko1_1.initial final TightSplit11.B (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)≤4 := by
  rw [←cut.outcomesEq];exact left
 have restCap : energy soko1_1.initial final UpperBudget11.Rest (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)≤2 := by
  rw [←cut.outcomesEq];exact rest
 have noNorth := FirstRest18711.quiet_count_zero cut.before
 exact ⟨prefix_colored cut.before.logged suffix completed prefixCheap leftCap restCap noNorth,
   prefix_down_zero cut.before.logged suffix completed prefixCheap leftCap restCap noNorth⟩
#print axioms prefix_colored
#print axioms prefix_down_zero
#print axioms before_first
end Owner1007.ModeCTopFacts11
