import Owner1007.FrontNoReturn26511
import Owner1007.EventBudgetTwo11
import Owner1007.MarkerQuietCheapPrefix11
import Owner1007.FrontNeighbor26511
import Owner1007.Side265Clear11
import Owner1007.Shaft18711Prices
import Owner1007.HeroEnergySlice11
namespace Owner1007.LeadingSideRestTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 (Rest)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem impossible {dirs final pushes moves outcomes}
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (below : ∃source,source∈endGroup Rest boundary.beforeOutcomes ∧
   boundary.actor.pushSource=some source ∧
   ((source=264∧boundary.direction=.east)∨(source=266∧boundary.direction=.west)∨(source=291∧boundary.direction=.north)))
 (restCap : energy soko1_1.initial final Rest outcomes≤2)
 (cut : FirstCut Front26511.paid boundary.actor.state [265] boundary.afterDirs final
   boundary.afterPushes boundary.afterMoves boundary.afterOutcomes)
 (side : cut.actor.pushSource=some 265 ∧(cut.direction=.east∨cut.direction=.west)) : False := by
 obtain ⟨source,sourceOwner,metadata,shape⟩ := below
 have target : pushTargets soko1_1.board source boundary.direction=[265] := by
  rcases shape with ⟨rfl,east⟩|⟨rfl,west⟩|⟨rfl,north⟩
  ·rw [east];decide +kernel
  ·rw [west];decide +kernel
  ·rw [north];decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect boundary.headChecked boundary.headEffect metadata target
   (by decide +kernel) boundary.before.logged.trace.holes_sublist.subset
 have effect : Matches boundary.middle boundary.actor (.push source (.stay 265)) := by simpa only [headEq] using boundary.headEffect
 let one : Logged soko1_1.board boundary.middle [boundary.direction] boundary.actor.state boundary.actor.pushCost 1 [boundary.headOutcome] :=
   .cons boundary.headChecked boundary.headEffect (.nil _)
 let firstAfter := boundary.before.logged.append one
 let firstSide := firstAfter.append cut.before.logged
 let effectsB := boundary.beforeOutcomes++[boundary.headOutcome]
 let effectsSide := effectsB++cut.beforeOutcomes
 have afterValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant firstAfter.trace
 have afterRest := firstAfter.end_subset (by decide) Rest (by decide) (by decide)
 have frontOwner : 265∈endGroup Rest effectsB := by
  rw [endGroup_append]
  change 265∈update (endGroup Rest boundary.beforeOutcomes) boundary.headOutcome
  rw [headEq]
  simp only [update,move,if_pos sourceOwner,post]
  exact List.mem_cons_self
 have frontActual : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
 have heroLower : boundary.actor.state.player∈Gate265Transport11.lower := by
  have playerEq : boundary.actor.state.player=source := by rw [effect.2]
  rw [playerEq]
  rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
 have good : OwnedCorral11.Good Front26511.locks Front26511.region boundary.actor.state [265] :=
  ⟨0,heroLower,by decide⟩
 obtain ⟨headSource,owner,headMetadata,_⟩ := cut.headPaid
 have same : headSource=265 := Option.some.inj (headMetadata.symm.trans side.1)
 have owner265 : 265∈endGroup [265] cut.beforeOutcomes := same ▸ owner
 have stationary := FrontNoReturn26511.stationary_if_present cut.before afterValid.1
   (by simpa using frontActual) good firstAfter.trace.holes_sublist.subset owner265
 have included := end_subset_selected cut.before.logged afterValid.1 [265] (endGroup Rest effectsB)
   (by decide) afterRest.1 (by simpa using frontOwner) afterRest.2
 have ownerRest : 265∈endGroup Rest effectsSide := by
  rw [endGroup_append]
  exact included owner265
 have facts := firstSide.end_subset (by decide) Rest (by decide) (by decide)
 have row := Shaft18711.exit_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant firstSide.trace)
   facts.1 facts.2 cut.headChecked cut.headEffect ⟨265,ownerRest,side.1,Or.inl ⟨rfl,side.2⟩⟩
 have allEffects : effectsSide++cut.headOutcome::cut.afterOutcomes=outcomes := by
  calc
   _=boundary.beforeOutcomes++boundary.headOutcome::(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by
    simp only [effectsSide,effectsB,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
   _=boundary.beforeOutcomes++boundary.headOutcome::boundary.afterOutcomes :=
    congrArg (fun rest=>boundary.beforeOutcomes++boundary.headOutcome::rest) cut.outcomesEq.symm
   _=outcomes := boundary.outcomesEq.symm
 have capHere : energy soko1_1.initial final Rest (effectsSide++cut.headOutcome::cut.afterOutcomes)≤2 := by
  rw [allEffects];exact restCap
 have prefixZero := EventBudgetTwo11.prefix_zero firstSide cut.headChecked cut.headEffect cut.after Rest
   (by decide) (by decide) row capHere
 change energy soko1_1.initial cut.middle Rest effectsSide=0 at prefixZero
 have markerInside (cell : Cell) (member : cell∈([264,266] : List Cell)) : [cell]⊆soko1_1.initial.boulders := by
  rcases List.mem_cons.mp member with rfl|later
  ·decide
  ·have eq : cell=266 := List.mem_singleton.mp later
   subst cell;decide
 have markerInRest (cell : Cell) (member : cell∈([264,266] : List Cell)) : [cell]⊆Rest := by
  rcases List.mem_cons.mp member with rfl|later
  ·decide
  ·have eq : cell=266 := List.mem_singleton.mp later
   subst cell;decide
 have markerCap (cell : Cell) (member : cell∈([264,266] : List Cell)) :
   energy soko1_1.initial cut.middle [cell] effectsSide≤0 := by
  have bound := energy_subset (Trace.nil soko1_1.initial) firstSide [cell] Rest
    (by simp) (by decide) (markerInRest cell member) (by decide) (by decide)
  change energy soko1_1.initial cut.middle [cell] effectsSide≤energy soko1_1.initial cut.middle Rest effectsSide at bound
  rw [prefixZero] at bound
  exact bound
 have fixedBefore (cell : Cell) (member : cell∈([264,266] : List Cell)) :
   ownPushes [cell] boundary.beforeOutcomes=0 := by
  have bound := prefix_energy_le boundary.before.logged (Logged.cons boundary.headChecked boundary.headEffect cut.before.logged)
    [cell] (by simp) (markerInside cell member)
  have eqPrefix : boundary.beforeOutcomes++boundary.headOutcome::cut.beforeOutcomes=effectsSide := by
   simp only [effectsSide,effectsB,List.append_assoc,List.singleton_append]
  rw [eqPrefix] at bound
  have price := markerCap cell member
  have cheap : energy soko1_1.initial boundary.middle [cell] boundary.beforeOutcomes<2 := by omega
  exact MarkerQuietCheapPrefix11.stationary boundary.before.logged boundary.before cell member cheap
 have sourceCases : source=264∨source=266∨source=291 := by
  rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
 obtain ⟨cell,member,different⟩ : ∃cell,cell∈([264,266] : List Cell) ∧source≠cell := by
  rcases sourceCases with rfl|rfl|rfl
  ·exact ⟨266,by decide,by decide⟩
  ·exact ⟨264,by decide,by decide⟩
  ·exact ⟨264,by decide,by decide⟩
 have tagBefore := no_push_unchanged [cell] boundary.beforeOutcomes (fixedBefore cell member)
 have tagAfter : endGroup [cell] effectsB=[cell] := by
  rw [endGroup_append,tagBefore]
  change update [cell] boundary.headOutcome=[cell]
  rw [headEq]
  have absent : source∉([cell] : List Cell) := by simpa only [List.mem_singleton] using different
  simp only [update,move,if_neg absent]
 have physical := (firstAfter.end_subset (by decide) [cell] (by simp) (markerInside cell member)).2
 have present : cell∈boundary.actor.state.boulders := physical (by rw [tagAfter];simp)
 have slice := slice_energy_le firstAfter cut.before.logged (Logged.nil cut.middle) [cell] (by simp) (markerInside cell member)
 change energy boundary.actor.state cut.middle (endGroup [cell] effectsB) cut.beforeOutcomes≤
   energy soko1_1.initial cut.middle [cell] ((effectsB++cut.beforeOutcomes)++[]) at slice
 rw [tagAfter,List.append_nil] at slice
 change energy boundary.actor.state cut.middle [cell] cut.beforeOutcomes≤energy soko1_1.initial cut.middle [cell] effectsSide at slice
 have capMarker := markerCap cell member
 have cheapLocal : energy boundary.actor.state cut.middle [cell] cut.beforeOutcomes<2 := by omega
 have kept := FrontNeighbor26511.tag cell member firstAfter.trace cut.before.logged frontActual present stationary cheapLocal
 have atSide := (cut.before.logged.end_subset afterValid.1 [cell] (by simp) (by simpa using present)).2
 have stillPresent : cell∈cut.middle.boulders := atSide (by rw [kept];simp)
 have clear := Side265Clear11.both cut.headChecked side.1 side.2
 rcases List.mem_cons.mp member with rfl|later
 ·exact clear.1 stillPresent
 ·have eq : cell=266 := List.mem_singleton.mp later
  subst cell
  exact clear.2 stillPresent
#print axioms impossible
end Owner1007.LeadingSideRestTwo11
