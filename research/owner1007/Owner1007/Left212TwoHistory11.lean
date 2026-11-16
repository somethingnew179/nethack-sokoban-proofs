import Owner1007.Left212History11
import Owner1007.Row212Above11
import Owner1007.SmallRestTopSplit11
import Owner1007.Left212TwoWord11
import Owner1007.SmallRestNoTopDown11
import Owner1007.SmallRestTopColor11
namespace Owner1007.Left212TwoHistory11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prefix_no_north {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (noRestNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0) :
 PaidCount11.count FirstRest18711.paid [212] dirs outcomes=0 := by
 rcases SmallRestTopSplit11.split prefixLog suffix completed cheap restCheap noRestNorth [212] (by decide) (by decide) with quiet|afterBoundary
 ·exact Row212Above11.no_north quiet
 ·obtain ⟨cut,afterZero⟩ := afterBoundary
  let tail := Logged.cons cut.headChecked cut.headEffect (cut.after.append suffix)
  have eqEffects : cut.beforeOutcomes++cut.headOutcome::(cut.afterOutcomes++last)=outcomes++last := by
   calc
    _=(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.cons_append]
    _=outcomes++last := congrArg (fun middle=>middle++last) cut.outcomesEq.symm
  have beforeCount := Row212Above11.no_north cut.before
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
 (completed : Goal final) (cheap : pushes<335)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) :
 PaidCount11.count FirstRest18711.paid [212] cut.beforeDirs cut.beforeOutcomes=0 := by
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have counts:=cut.pushesEq
 have prefixCheap : cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)<335 := by omega

 exact prefix_no_north cut.before.logged suffix completed prefixCheap (by rw [←cut.outcomesEq];exact restCheap) (FirstRest18711.quiet_count_zero cut.before)

theorem at_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes<335)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes)
 (cheap212 : energy soko1_1.initial final [212] outcomes<4) :
 ∃dest,dest∈([211,212,214]:List Cell) ∧endGroup [212] cut.beforeOutcomes=[dest] := by
 have northZero := before_first logged completed cheap restCheap cut
 have downTop := SmallRestNoTopDown11.before_first logged completed cheap restCheap cut
 have quietDownTop := QuietFromCount11.from_count cut.before.logged Gate265Transport11.upperOrigins downTop
 have quietDown212 := TransportQuiet11.Quiet.project quietDownTop (by decide) (by decide) (by decide)
   [212] (by decide) (by decide)
 have down212 := FirstRest18711.quiet_count_zero quietDown212
 have quietEarly := QuietFromCount11.from_two_counts cut.before.logged [212] northZero down212
 have exactQuiet : UpperQuiet11.Quiet Left212Word11.early soko1_1.initial [212]
     cut.beforeDirs cut.middle cut.beforePushes cut.beforeMoves cut.beforeOutcomes := quietEarly
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have prefixBound := prefix_energy_le cut.before.logged suffix [212] (by decide) (by decide)
 have prefixCheap : energy soko1_1.initial cut.middle [212] cut.beforeOutcomes<4 := by
   rw [←cut.outcomesEq] at prefixBound
   omega
 obtain ⟨dest,member,tag⟩ := Left212TwoWord11.guard_logged exactQuiet
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide) prefixCheap
 have selected := cut.before.logged.end_subset (by decide) [212] (by decide) (by decide)
 have pairSelected := cut.before.logged.end_subset (by decide) ([212]++UpperBudget11.Rest) (by decide) (by decide)
 have pairPerm := HeroLedger.Logged.end_append_perm cut.before.logged (by decide)
   [212] UpperBudget11.Rest (by decide) (by decide)
 have separate := (List.nodup_append.mp (pairPerm.nodup_iff.mp pairSelected.1)).2.2
 obtain ⟨source,restOwner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 have hero : cut.middle.player=239 := by
  have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
  exact ActorPrices11.support_of_check 213 cut.middle.player .north 239 (by decide +kernel)
    (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked metadata)
 have noHeroBox : 239∉cut.middle.boulders := by
  have clear := (step_player_clear _ _ _ _ cut.headChecked).2.2.1
  simpa only [hero] using clear
 have included := end_subset_selected cut.before.logged (by decide) [212] Gate265Transport11.upperOrigins
   (by decide) (by decide) (by decide) (by decide)
 have colored := SmallRestTopColor11.before_first logged completed cheap restCheap cut
 have insideUpper : dest∈Gate265Transport11.upper := colored (included (by rw [tag];simp))
 change dest∈([212,213,239,265,211,214,264,266] : List Cell) at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact ⟨212,by decide,tag⟩
 ·exact False.elim (separate 213 (by rw [tag];simp) 213 restOwner rfl)
 ·exact False.elim (noHeroBox (selected.2 (by rw [tag];simp)))
 ·exact False.elim ((show (265:Cell)∉Gate265Transport11.upper from by decide) insideUpper)
 ·exact ⟨211,by decide,tag⟩
 ·exact ⟨214,by decide,tag⟩
 ·exact False.elim ((show (264:Cell)∉Gate265Transport11.upper from by decide) insideUpper)
 ·exact False.elim ((show (266:Cell)∉Gate265Transport11.upper from by decide) insideUpper)
#print axioms prefix_no_north
#print axioms before_first
#print axioms at_first
end Owner1007.Left212TwoHistory11
