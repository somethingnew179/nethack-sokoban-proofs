import Owner1007.Left212History11
import Owner1007.TightTailConsumed11
import Owner1007.Arrival187Left21211
import Owner1007.LeftSameActor11
import Owner1007.HeroEnergySlice11
namespace Owner1007.Left186Excluded11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (four186 : 4≤energy soko1_1.initial final [186] outcomes) : False := by
 obtain ⟨_,upper,left,rest⟩ := Tight32511.budgets logged completed cheap
 have split := HeroLedger.Logged.energy_split logged (by decide) weightAt NetHack.Soko11Hero315.holeWeight
   [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final [186,212] outcomes=
   energy soko1_1.initial final [186] outcomes+energy soko1_1.initial final [212] outcomes at split
 change energy soko1_1.initial final [186,212] outcomes=4 at left
 have nn212 := energy_nonnegative logged [212] (by decide) (by decide)
 have zero212 : energy soko1_1.initial final [212] outcomes=0 := by omega
 obtain ⟨cut⟩ := FirstRest18711.first_cut logged completed cheap
 have before212 := Left212History11.at_first logged completed cheap cut (by omega)
 have shape := FirstRest18711.head_shape cut
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 187)) := by simpa only [shape.2.2] using cut.headEffect
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
 let first := cut.before.logged.append one
 have firstCheap : cut.beforePushes+cut.actor.pushCost+cut.afterPushes≤325 := by
   have counts:=cut.pushesEq
   omega
 have tag212 : endGroup [212] (cut.beforeOutcomes++[cut.headOutcome])=[212] := by
   rw [endGroup_append,before212]
   change update [212] cut.headOutcome=[212]
   rw [shape.2.2]
   decide
 have actual212 := (first.end_subset (by decide) [212] (by decide) (by decide)).2
 have inside : ([187,212] : List Cell)⊆cut.actor.state.boulders := by
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   ·rw [effect.2];simp
   ·exact actual212 (by rw [tag212];simp)
 have hero : cut.actor.state.player∈Arrival187Left21211.region 0 := by
   have same : cut.actor.state.player=213 := by rw [effect.2]
   rw [same]
   exact Arrival187Left21211.hero213
 have gone := TightTailConsumed11.gone first cut.after completed firstCheap [187,212] (by decide) inside
 have allEffects : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
   simpa only [List.append_assoc,List.singleton_append] using cut.outcomesEq.symm
 have globalRestZero : energy soko1_1.initial final UpperBudget11.Rest
     ((cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes)=0 := by rw [allEffects];exact rest
 have currentRest : 187∈endGroup UpperBudget11.Rest (cut.beforeOutcomes++[cut.headOutcome]) := by
   rw [endGroup_append]
   change 187∈update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome
   rw [shape.2.2]
   simp only [update,move,if_pos owner,post]
   simp
 have restZero := ZeroRestTail11.subset_zero first cut.after globalRestZero [187] (by decide) (by simpa using currentRest)
 have paid212 := Arrival187Left21211.left_two_if_rest_zero first.trace cut.after inside hero gone restZero
 have slice := slice_energy_le first cut.after (Logged.nil final) [212] (by decide) (by decide)
 change energy cut.actor.state final (endGroup [212] (cut.beforeOutcomes++[cut.headOutcome])) cut.afterOutcomes≤
   energy soko1_1.initial final [212] (((cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes)++[]) at slice
 rw [tag212,allEffects,List.append_nil,zero212] at slice
 omega

theorem only_second_actor {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 4≤energy soko1_1.initial final [212] outcomes := by
 rcases LeftSameActor11.canonical_actor_four logged completed cheap with first|second
 ·exact False.elim (not_four logged completed cheap first)
 ·exact second
#print axioms not_four
#print axioms only_second_actor
end Owner1007.Left186Excluded11
