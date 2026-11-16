import Owner1007.ModeC212History11
import Owner1007.RestArrivalFour11
import Owner1007.Arrival187Four11
import Owner1007.RestTailBudget11
import Owner1007.Budget32711
import Owner1007.LeftSameActor11
import Owner1007.Zero186Strong32711
namespace Owner1007.ModeCLeft11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2)
 (four186 : 4≤energy soko1_1.initial final [186] outcomes) : False := by
 have split := HeroLedger.Logged.energy_split logged (by decide) weightAt NetHack.Soko11Hero315.holeWeight
   [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final TightSplit11.B outcomes=
   energy soko1_1.initial final [186] outcomes+energy soko1_1.initial final [212] outcomes at split
 have nn212 := energy_nonnegative logged [212] (by decide) (by decide)
 have zero212 : energy soko1_1.initial final [212] outcomes=0 := by omega
 have gone212 := TightSurvivors11.singleton_nil logged completed TightSplit11.B (by decide) (by decide) (by decide)
   4 left 212 (by decide) (by decide +kernel)
 obtain ⟨cut⟩ := RestArrivalFour11.first_cut logged completed (by omega)
 have before212 := ModeC212History11.at_first logged completed cheap left rest cut (by omega)
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
 have hero : cut.actor.state.player=213 := by rw [effect.2]
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
 have leftBound := slice_energy_le first cut.after (Logged.nil final) [212] (by decide) (by decide)
 change energy cut.actor.state final (endGroup [212] (cut.beforeOutcomes++[cut.headOutcome])) cut.afterOutcomes≤
   energy soko1_1.initial final [212] (((cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes)++[]) at leftBound
 rw [tag212,allEffects,List.append_nil,zero212] at leftBound
 have goneTail : endGroup [212] cut.afterOutcomes=[] := by
   rw [←allEffects,endGroup_append,tag212] at gone212
   exact gone212
 rcases Arrival187Four11.dichotomy first.trace cut.after inside hero goneTail with four|two <;> omega

theorem zero186 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2) :
 energy soko1_1.initial final [186] outcomes=0 := by
 have gone := Budget32711.left_gone logged completed (by omega)
 have counts := LeftSameActor11.count_two_one_actor logged completed left gone
 have split := Hero315Frame11.energy_split logged [186] [212] (by decide) (by decide)
 change energy soko1_1.initial final TightSplit11.B outcomes=
   energy soko1_1.initial final [186] outcomes+energy soko1_1.initial final [212] outcomes at split
 have nn186 := energy_nonnegative logged [186] (by decide) (by decide)
 rcases counts with first|second
 ·exact False.elim (not_four logged completed cheap left rest (LeftActorCount11.actor_four logged 186 (by decide) first))
 ·have actorFour := LeftActorCount11.actor_four logged 212 (by decide) second
  omega

theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (upper : energy soko1_1.initial final UpperBudget11.U6 outcomes≤8)
 (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2) : False :=
 Zero186Strong32711.impossible logged completed cheap upper (by omega) (zero186 logged completed cheap left rest)
#print axioms not_four
#print axioms zero186
#print axioms impossible
end Owner1007.ModeCLeft11
