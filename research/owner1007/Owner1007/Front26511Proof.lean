import Owner1007.Front26511Geometry
import Owner1007.GrowingCorral11
import Owner1007.Shaft18711Prices
import Owner1007.LoggedEventGap11
import Owner1007.FirstRest18711
import Owner1007.HeroEndSubset11
namespace Owner1007.Front26511
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem quiet_of_no_north {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes++last)=0)
 (group : List Cell) (groupUnique : group.Nodup) (inRest : group⊆endGroup UpperBudget11.Rest before)
 (noNorth : PaidCount11.count FirstRest18711.paid (endGroup UpperBudget11.Rest before) dirs outcomes=0) :
 UpperQuiet11.Quiet paid state group dirs middle pushes moves outcomes := by
 have restBefore := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 rcases first_cut_or_quiet (paid:=paid) logged group with found|quiet
 ·obtain ⟨cut⟩ := found
  obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
  have included := end_subset_selected cut.before.logged valid.1 group (endGroup UpperBudget11.Rest before)
    groupUnique restBefore.1 inRest restBefore.2
  have localRestOwner : source∈endGroup (endGroup UpperBudget11.Rest before) cut.beforeOutcomes := included owner
  have rootRestOwner : source∈endGroup UpperBudget11.Rest (before++cut.beforeOutcomes) := by
    rw [endGroup_append]
    exact localRestOwner
  change Shaft18711.paid source cut.direction at pays
  rcases pays with north|positive
  ·have northPaid : OwnedCorral11.PaidStep FirstRest18711.paid
      (endGroup (endGroup UpperBudget11.Rest before) cut.beforeOutcomes) cut.direction cut.actor :=
      ⟨source,localRestOwner,metadata,north⟩
   have counted := PaidCount11.event_le (paid:=FirstRest18711.paid)
     (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes) cut.before.logged cut.headEffect
     (endGroup UpperBudget11.Rest before) northPaid
   rw [←cut.dirsEq,←cut.outcomesEq,noNorth] at counted
   omega
  ·let headFirst := first.append cut.before.logged
   have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant headFirst.trace
   have currentRest := headFirst.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
   have row := Shaft18711.exit_row currentValid currentRest.1 currentRest.2 cut.headChecked cut.headEffect
     ⟨source,rootRestOwner,metadata,positive⟩
   let tail := cut.after.append suffix
   have gap := logged_event_gap_le headFirst cut.headChecked cut.headEffect tail UpperBudget11.Rest (by decide) (by decide)
   have bound := Int.le_trans row gap
   change 2≤energy soko1_1.initial final UpperBudget11.Rest
     ((before++cut.beforeOutcomes)++cut.headOutcome::(cut.afterOutcomes++last)) at bound
   have eqEffects : (before++cut.beforeOutcomes)++cut.headOutcome::(cut.afterOutcomes++last)=before++outcomes++last := by
     calc
       _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.cons_append]
       _=before++outcomes++last := congrArg (fun middle=>before++middle++last) cut.outcomesEq.symm
   rw [eqEffects,zeroRest] at bound
   omega
 ·exact quiet

theorem top_untouched {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes++last)=0)
 (front : 265∈endGroup UpperBudget11.Rest before)
 (noNorth : PaidCount11.count FirstRest18711.paid (endGroup UpperBudget11.Rest before) dirs outcomes=0)
 (top : List Cell) (bothUnique : (([265] : List Cell)++top).Nodup)
 (bothInside : ([265] : List Cell)++top⊆state.boulders)
 (hero : state.player∈Gate265Transport11.lower)
 (outside : ∀c,c∈top→c∉Gate265Transport11.lower) :
 ownPushes top outcomes=0 := by
 have quiet := quiet_of_no_north first logged suffix zeroRest [265] (by simp) (by simpa using front) noNorth
 have actualUnique := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have good : GrowingCorral11.Separated locks region state [265] top := by
   refine ⟨⟨0,by decide⟩,?_,?_,?_⟩
   ·change state.player∈Gate265Transport11.lower
    exact hero
   ·change ([265] : List Cell)⊆[265]
    decide
   ·change ∀c,c∈top→c∉Gate265Transport11.lower
    exact outside
 exact (GrowingCorral11.Quiet.separated_untouched closed unique growth quiet actualUnique bothUnique bothInside good first.trace.holes_sublist.subset).2
#print axioms quiet_of_no_north
#print axioms top_untouched
end Owner1007.Front26511
