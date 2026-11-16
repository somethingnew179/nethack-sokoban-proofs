import Owner1007.Left186Excluded326Core11
namespace Owner1007.RestLeft212Ticket11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem sum_at_least_two_capacity {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheapP : pushes<335)
 (capacity : ¬([187,212] : List Cell)⊆final.boulders) :
 2≤energy soko1_1.initial final UpperBudget11.Rest outcomes+
   energy soko1_1.initial final [212] outcomes := by
 apply Int.le_of_not_gt
 intro insufficient
 have nnRest := energy_nonnegative logged UpperBudget11.Rest (by decide) (by decide)
 have nn212 := energy_nonnegative logged [212] (by decide) (by decide)
 have restCheap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2 := by omega
 have cheap212 : energy soko1_1.initial final [212] outcomes<2 := by omega
 obtain ⟨cut⟩ := RestArrivalTwo11.first_cut logged completed restCheap
 have before212 := SmallRest212History11.at_first logged completed cheapP restCheap cut cheap212
 have shape := FirstRest18711.head_shape cut
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 187)) := by simpa only [shape.2.2] using cut.headEffect
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
 let first := cut.before.logged.append one
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
 have allEffects : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes=outcomes := by
   simpa only [List.append_assoc,List.singleton_append] using cut.outcomesEq.symm
 have currentRest : 187∈endGroup UpperBudget11.Rest (cut.beforeOutcomes++[cut.headOutcome]) := by
   rw [endGroup_append]
   change 187∈update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome
   rw [shape.2.2]
   simp only [update,move,if_pos owner,post]
   simp
 have restBound := RestTailBudget11.subset_le first cut.after [187] (by decide) (by simpa using currentRest)
 rw [allEffects] at restBound
 have pairTicket := Arrival187PairCapacity11.future_two first.trace cut.after inside hero capacity
 have pairSplit := HeroLedger.Logged.energy_split cut.after
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1 weightAt NetHack.Soko11Hero315.holeWeight
   [187] [212] (by decide) inside
 change energy cut.actor.state final [187,212] cut.afterOutcomes=
   energy cut.actor.state final [187] cut.afterOutcomes+energy cut.actor.state final [212] cut.afterOutcomes at pairSplit
 have slice := slice_energy_le first cut.after (Logged.nil final) [212] (by decide) (by decide)
 change energy cut.actor.state final (endGroup [212] (cut.beforeOutcomes++[cut.headOutcome])) cut.afterOutcomes≤
   energy soko1_1.initial final [212] (((cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes)++[]) at slice
 rw [tag212,allEffects,List.append_nil] at slice
 omega

#print axioms sum_at_least_two_capacity
end Owner1007.RestLeft212Ticket11
