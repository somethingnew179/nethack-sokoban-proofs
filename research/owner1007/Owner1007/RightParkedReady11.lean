import Owner1007.RightParkedSix11Data
import Owner1007.BlockRest18611
import Owner1007.BlockRestNorth11
import Owner1007.Upper188At18611
namespace Owner1007.RightParkedReady11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RightParkedSix11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
structure Ready {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (i : Fin 4) : Prop where
 completed : Goal final
 cheap : beforePushes+pushes≤327
 upper : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6
 left186 : energy soko1_1.initial final [186] (before++outcomes)≤4
 left212 : energy soko1_1.initial final [212] (before++outcomes)≤2
 rest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2
 noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest beforeDirs before=0
 zero137 : ownPushes [137] before=0
 zero139 : ownPushes [139] before=0
 tag186 : endGroup [186] before=[184]
 tag188 : endGroup [188] before=[u i]
 tag191 : endGroup [191] before=[189]
 tag212 : endGroup [212] before=[marker i]
 pairTwo : 2≤energy soko1_1.initial state TightSplit11.A before
 upperFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before
 physical : locks i⊆state.boulders
 hero : state.player∈region i
 gone : endGroup (locks i) outcomes=[]

theorem member_zero {state dirs final pushes moves outcomes i}
 (quiet : UpperQuiet11.Quiet paid state (locks i) dirs final pushes moves outcomes)
 (cell : Cell) (member : cell∈locks i) : ownPushes [cell] outcomes=0:=by
 exact LeftQuietIdentity11.subset_zero [cell] (locks i) outcomes (by simpa using member)
  (QuietGroupFixed11.whole_fixed quiet (by intro c h d;trivial))

theorem before_ready {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes i}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (ready : Ready first logged i)
 (cut : FirstCut paid state (locks i) dirs final pushes moves outcomes)
 (heroBefore : cut.middle.player∈region i) :
 Ready (first.append cut.before.logged) (Logged.cons cut.headChecked cut.headEffect cut.after) i:=by
 have zero:=QuietGroupFixed11.whole_fixed cut.before (by intro c h d;trivial)
 have fixed:=no_push_unchanged (locks i) cut.beforeOutcomes zero
 have localFixed (cell : Cell) (member : cell∈locks i) : endGroup [cell] cut.beforeOutcomes=[cell]:=
  no_push_unchanged [cell] cut.beforeOutcomes (member_zero cut.before cell member)
 have tags (cell : Cell) (target : Cell) (tag : endGroup [cell] before=[target]) (member : target∈locks i) :
  endGroup [cell] (before++cut.beforeOutcomes)=[target]:=by rw [endGroup_append,tag,localFixed target member]
 have gateZero (cell : Cell) (z : ownPushes [cell] before=0) (member : cell∈locks i) :
  ownPushes [cell] (before++cut.beforeOutcomes)=0:=by
  rw [ownPushes_append,no_push_unchanged _ _ z,z,member_zero cut.before cell member]
 have wholeEq : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by
  rw [List.append_assoc,←cut.outcomesEq]
 have localNoRest : PaidCount11.count FirstRest18711.paid (endGroup UpperBudget11.Rest before) cut.beforeDirs cut.beforeOutcomes=0:=by
  have ui : u i=186∨u i=187:=by unfold u;split<;>simp
  rcases ui with at186|at187
  ·have member : 186∈locks i:=by simp [locks,at186]
   exact BlockRest18611.count_zero first cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
    ready.completed (by have eq:=cut.pushesEq;have cap:=ready.cheap;omega) (ready.physical member)
    (member_zero cut.before 186 member) _
  ·have member : 187∈locks i:=by simp [locks,at187]
   exact BlockRestNorth11.count_zero cut.before.logged 187 (Or.inl rfl) (ready.physical member)
    (member_zero cut.before 187 member) _
 have facts:=cut.before.logged.end_subset (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
  (locks i) (unique i) ready.physical
 have prefixPair:=prefix_energy_le first cut.before.logged TightSplit11.A (by decide) (by decide)
 have prefixUpper:=prefix_energy_le first cut.before.logged UpperBudget11.U6 (by decide) (by decide)
 refine ⟨ready.completed,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,heroBefore,?_⟩
 ·have eq:=cut.pushesEq;have cap:=ready.cheap;change beforePushes+cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤327;omega
 ·change energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤6
  rw [wholeEq];exact ready.upper
 ·change energy soko1_1.initial final [186] ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤4
  rw [wholeEq];exact ready.left186
 ·change energy soko1_1.initial final [212] ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤2
  rw [wholeEq];exact ready.left212
 ·change energy soko1_1.initial final UpperBudget11.Rest ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)<2
  rw [wholeEq];exact ready.rest
 ·change PaidCount11.count FirstRest18711.paid UpperBudget11.Rest (beforeDirs++cut.beforeDirs) (before++cut.beforeOutcomes)=0
  rw [PaidCount11.append first,ready.noRest,localNoRest]
 ·exact gateZero 137 ready.zero137 (by simp [locks])
 ·exact gateZero 139 ready.zero139 (by simp [locks])
 ·exact tags 186 184 ready.tag186 (by simp [locks])
 ·exact tags 188 (u i) ready.tag188 (by simp [locks])
 ·exact tags 191 189 ready.tag191 (by simp [locks])
 ·exact tags 212 (marker i) ready.tag212 (by simp [locks])
 ·change 2≤energy soko1_1.initial cut.middle TightSplit11.A (before++cut.beforeOutcomes);have cap:=ready.pairTwo;omega
 ·change 4≤energy soko1_1.initial cut.middle UpperBudget11.U6 (before++cut.beforeOutcomes);have cap:=ready.upperFour;omega
 ·simpa only [fixed] using facts.2
 ·change endGroup (locks i) (cut.headOutcome::cut.afterOutcomes)=[]
  have gone:=ready.gone
  rw [cut.outcomesEq,endGroup_append,fixed] at gone
  exact gone
#print axioms before_ready
end Owner1007.RightParkedReady11
