import Owner1007.Left212QuietNorth11
import Owner1007.TopBefore187Split11
import Owner1007.Left212AtFirst18711
namespace Owner1007.Left212History11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prefix_no_north {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes≤325)
 (noRestNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (cheap212 : energy soko1_1.initial final [212] (outcomes++last)<2) :
 PaidCount11.count FirstRest18711.paid [212] dirs outcomes=0 := by
 rcases TopBefore187Split11.split prefixLog suffix completed cheap noRestNorth [212] (by decide) (by decide) with quiet|afterBoundary
 ·exact Left212QuietNorth11.no_north prefixLog suffix completed cheap quiet cheap212
 ·obtain ⟨cut,afterZero⟩ := afterBoundary
  let tail := Logged.cons cut.headChecked cut.headEffect (cut.after.append suffix)
  have eqEffects : cut.beforeOutcomes++cut.headOutcome::(cut.afterOutcomes++last)=outcomes++last := by
   calc
    _=(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.cons_append]
    _=outcomes++last := congrArg (fun middle=>middle++last) cut.outcomesEq.symm
  have beforeCheap : cut.beforePushes+(cut.actor.pushCost+(cut.afterPushes+lastPushes))≤325 := by
   have counts:=cut.pushesEq
   omega
  have before212Cheap : energy soko1_1.initial final [212] (cut.beforeOutcomes++cut.headOutcome::(cut.afterOutcomes++last))<2 := by
   rw [eqEffects]
   exact cheap212
  have beforeCount := Left212QuietNorth11.no_north cut.before.logged tail completed beforeCheap cut.before before212Cheap
  have afterCount := TransportEvents11.count_le_ownPushes FirstRest18711.paid (endGroup [212] cut.beforeOutcomes)
    (cut.direction::cut.afterDirs) (cut.headOutcome::cut.afterOutcomes)
  have tailZero : PaidCount11.count FirstRest18711.paid (endGroup [212] cut.beforeOutcomes)
      (cut.direction::cut.afterDirs) (cut.headOutcome::cut.afterOutcomes)=0 := by omega
  have allZero : PaidCount11.count FirstRest18711.paid [212]
      (cut.beforeDirs++cut.direction::cut.afterDirs) (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=0 := by
   rw [PaidCount11.append cut.before.logged,beforeCount,tailZero]
  simpa only [←cut.dirsEq,←cut.outcomesEq] using allZero

theorem before_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes)
 (cheap212 : energy soko1_1.initial final [212] outcomes<2) :
 PaidCount11.count FirstRest18711.paid [212] cut.beforeDirs cut.beforeOutcomes=0 := by
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have counts:=cut.pushesEq
 have prefixCheap : cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤325 := by omega
 have cheapTag : energy soko1_1.initial final [212] (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)<2 := by
   rw [←cut.outcomesEq]
   exact cheap212
 exact prefix_no_north cut.before.logged suffix completed prefixCheap (FirstRest18711.quiet_count_zero cut.before) cheapTag

theorem at_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes)
 (cheap212 : energy soko1_1.initial final [212] outcomes<2) :
 endGroup [212] cut.beforeOutcomes=[212] :=
 Left212AtFirst18711.at_first logged completed cheap cut (before_first logged completed cheap cut cheap212) cheap212
#print axioms prefix_no_north
#print axioms before_first
#print axioms at_first
end Owner1007.Left212History11
