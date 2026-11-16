import Owner1007.UpperFirstCut11
import Owner1007.ZeroRestTail11
import Owner1007.HeroEndSubset11
import Owner1007.LoggedAppend11
namespace Owner1007.RestCutAdvance11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def headLog {paid state group dirs final pushes moves outcomes}
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :
 Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
 .cons cut.headChecked cut.headEffect (.nil _)
def localLog {paid state group dirs final pushes moves outcomes}
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :=
 cut.before.logged.append (headLog cut)
def afterLog {beforeDirs state beforePushes beforeMoves before paid group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :=
 first.append (localLog cut)
def afterPrefix {beforeDirs state beforePushes beforeMoves before paid group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut paid state group dirs final pushes moves outcomes) : List Outcome :=
 before++(cut.beforeOutcomes++[cut.headOutcome])
def next {paid state group dirs final pushes moves outcomes}
 (cut : FirstCut paid state group dirs final pushes moves outcomes) : List Cell :=
 update (endGroup group cut.beforeOutcomes) cut.headOutcome
theorem effects {beforeDirs state beforePushes beforeMoves before paid group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut paid state group dirs final pushes moves outcomes) :
 afterPrefix first cut++cut.afterOutcomes=before++outcomes := by
 unfold afterPrefix
 calc
   _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
   _=before++outcomes := congrArg (fun rest=>before++rest) cut.outcomesEq.symm
theorem subset_after {beforeDirs state beforePushes beforeMoves before paid group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (groupUnique : group.Nodup) (subset : group⊆endGroup UpperBudget11.Rest before) :
 next cut⊆endGroup UpperBudget11.Rest (afterPrefix first cut) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have big := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have inclusion := end_subset_selected (localLog cut) valid.1 group (endGroup UpperBudget11.Rest before)
   groupUnique big.1 subset big.2
 intro c member
 have member' : c∈endGroup group (cut.beforeOutcomes++[cut.headOutcome]) := by
   simpa only [next,endGroup_append,endGroup] using member
 have included := inclusion member'
 change c∈endGroup UpperBudget11.Rest (before++(cut.beforeOutcomes++[cut.headOutcome]))
 rw [endGroup_append]
 exact included
theorem zero_after {beforeDirs state beforePushes beforeMoves before paid group dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut paid state group dirs final pushes moves outcomes)
 (groupUnique : group.Nodup) (subset : group⊆endGroup UpperBudget11.Rest before)
 (zero : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)=0)
 (selected : List Cell) (selectedUnique : selected.Nodup) (inside : selected⊆next cut) :
 energy cut.actor.state final selected cut.afterOutcomes=0 := by
 have selectedInside := List.Subset.trans inside (subset_after first cut groupUnique subset)
 apply ZeroRestTail11.subset_zero (afterLog first cut) cut.after _ selected selectedUnique selectedInside
 change energy soko1_1.initial final UpperBudget11.Rest (afterPrefix first cut++cut.afterOutcomes)=0
 rw [effects first cut]
 exact zero
#print axioms subset_after
#print axioms zero_after
end Owner1007.RestCutAdvance11