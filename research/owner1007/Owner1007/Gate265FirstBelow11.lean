import Owner1007.Gate265Above11Proof
import Owner1007.Gate265Markers11
namespace Owner1007.Gate265FirstBelow11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem not_above {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes) :
 ¬(boundary.actor.pushSource=some 239∧boundary.direction=.south) := by
 rintro ⟨metadata,south⟩
 have zeroRest := (Tight32511.budgets logged completed cheap).2.2.2
 have target : pushTargets soko1_1.board 239 boundary.direction=[265] := by rw [south];decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect boundary.headChecked boundary.headEffect metadata target
   (by decide +kernel) boundary.before.logged.trace.holes_sublist.subset
 have effect : Matches boundary.middle boundary.actor (.push 239 (.stay 265)) := by simpa only [headEq] using boundary.headEffect
 let headLog : Logged soko1_1.board boundary.middle [boundary.direction] boundary.actor.state boundary.actor.pushCost 1 [boundary.headOutcome] :=
   .cons boundary.headChecked boundary.headEffect (.nil _)
 let first := boundary.before.logged.append headLog
 have beforeRest := boundary.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have markerBefore (cell : Cell) (member : cell∈([264,266] : List Cell)) :
   cell∈endGroup UpperBudget11.Rest boundary.beforeOutcomes := by
   have fixed := Gate265Markers11.stationary_before logged zeroRest boundary cell member
   have tag := no_push_unchanged [cell] boundary.beforeOutcomes fixed
   have initial : [cell]⊆UpperBudget11.Rest := by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> decide
   have included := end_subset_selected boundary.before.logged (by decide) [cell] UpperBudget11.Rest
     (by simp) (by decide) initial (by decide)
   exact included (by rw [tag];simp)
 have nextMarkers : ([264,266] : List Cell)⊆endGroup UpperBudget11.Rest (boundary.beforeOutcomes++[boundary.headOutcome]) := by
   intro cell member
   have owner := markerBefore cell member
   have different : cell≠239 := by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> decide
   rw [endGroup_append]
   change cell∈update (endGroup UpperBudget11.Rest boundary.beforeOutcomes) boundary.headOutcome
   rw [headEq]
   by_cases sourceOwner : 239∈endGroup UpperBudget11.Rest boundary.beforeOutcomes
   ·simp only [update,move,if_pos sourceOwner,post]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne different).mpr owner)
   ·simpa only [update,move,if_neg sourceOwner] using owner
 have hero : boundary.actor.state.player=239 := by rw [effect.2]
 have front : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
 have obstruction := Gate265Above11.future_obstruction first boundary.after completed hero front nextMarkers
 have eqEffects : (boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes=outcomes := by
   simpa only [List.append_assoc,List.singleton_append] using boundary.outcomesEq.symm
 rcases obstruction with restPaid|deep
 ·change 2≤energy soko1_1.initial final UpperBudget11.Rest
     ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes) at restPaid
  rw [eqEffects,zeroRest] at restPaid
  omega
 ·change 335≤boundary.beforePushes+boundary.actor.pushCost+boundary.afterPushes at deep
  have counts := boundary.pushesEq
  omega

theorem lower_owner {dirs final pushes moves outcomes}
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (source : Cell) (member : source∈([264,266,291] : List Cell))
 (owner : source∈endGroup soko1_1.initial.boulders boundary.beforeOutcomes) :
 source∈endGroup UpperBudget11.Rest boundary.beforeOutcomes := by
 have partition := (endGroup_perm Gate265Transport11.original_partition boundary.beforeOutcomes).symm.trans
   (HeroLedger.Logged.end_append_perm boundary.before.logged (by decide)
     Gate265Transport11.upperOrigins Gate265Transport11.lowerOrigins (by decide) (by decide))
 have split := List.mem_append.mp (partition.mem_iff.mp owner)
 have inLower : source∈endGroup Gate265Transport11.lowerOrigins boundary.beforeOutcomes := by
   rcases split with upper|lower
   ·have colored := Gate265Transport11.quiet_upper boundary.before upper
    have notUpper : source∉Gate265Transport11.upper := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> decide
    exact False.elim (notUpper colored)
   ·exact lower
 have included := end_subset_selected boundary.before.logged (by decide) Gate265Transport11.lowerOrigins UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide)
 exact included inLower

theorem below {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes) :
 ∃source, source∈endGroup UpperBudget11.Rest boundary.beforeOutcomes ∧
   boundary.actor.pushSource=some source ∧
   ((source=264∧boundary.direction=.east)∨(source=266∧boundary.direction=.west)∨(source=291∧boundary.direction=.north)) := by
 obtain ⟨source,owner,metadata,pays⟩ := boundary.headPaid
 rcases pays with ⟨rfl,south⟩|⟨rfl,east⟩|⟨rfl,west⟩|⟨rfl,north⟩
 ·exact False.elim (not_above logged completed cheap boundary ⟨metadata,south⟩)
 ·exact ⟨264,lower_owner boundary 264 (by decide) owner,metadata,Or.inl ⟨rfl,east⟩⟩
 ·exact ⟨266,lower_owner boundary 266 (by decide) owner,metadata,Or.inr (Or.inl ⟨rfl,west⟩)⟩
 ·exact ⟨291,lower_owner boundary 291 (by decide) owner,metadata,Or.inr (Or.inr ⟨rfl,north⟩)⟩
#print axioms not_above
#print axioms lower_owner
#print axioms below
end Owner1007.Gate265FirstBelow11
