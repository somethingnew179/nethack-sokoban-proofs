import Owner1007.UpperEventEnergy11
import Owner1007.UpperHeadCases11
import Owner1007.UpperReset11
import Owner1007.Upper190After11
import Owner1007.Upper216After11
import Owner1007.StationaryExit11
import Owner1007.ParkedEnergy11
import Owner1007.PostEnergy11
namespace Owner1007.UpperReserve11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

theorem upper_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final) :
 4≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 4≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<4 := by omega
   obtain ⟨cut⟩ := first_cut logged completed
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have afterReached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have facts := next_facts cut
   have afterCheap := suffix_cheap cut cheap
   have cap : ∀ small : List Cell, small.Nodup → small⊆nextGroup cut →
       energy cut.actor.state final small cut.afterOutcomes<2 := by
     intro small unique subset
     have bound := energy_subset afterReached cut.after small (nextGroup cut) unique facts.1 subset facts.2.1 facts.2.2
     omega
   have upperBefore := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
   have upperAfterUnique := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ upperBefore.1 upperBefore.2
   have upperAfterInside := GhostSubset.update_subset _ _ _ cut.headEffect _ upperBefore.1 upperBefore.2
   have upperBeforeSize := endGroup_length_le originalGroup cut.beforeOutcomes
   change (endGroup originalGroup cut.beforeOutcomes).length≤3 at upperBeforeSize
   have upperAfterSize : (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome).length≤3 :=
     Nat.le_trans (update_length _ _) upperBeforeSize
   have upperBeforeSubset := end_subset_selected cut.before.logged (by decide) originalGroup U6
     (by decide) (by decide) (by decide) (by decide)
   have upperAfterSubset := update_mono _ _ upperBefore.1 upperBeforeSubset cut.headOutcome
   have excludeReset : OwnedCorral11.Good UpperZero11.locks UpperZero11.region cut.actor.state
       (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome) → False := by
     intro good
     have future := CutEnergy11.future_energy UpperZero11.closed UpperZero11.unique UpperZero11.size
       (by decide) CutEnergy11.upper_paid afterReached cut.after completed _ upperAfterUnique upperAfterInside upperAfterSize good
     have bound := cap _ upperAfterUnique upperAfterSubset
     omega
   rcases UpperHeadCases11.FirstCut.head_cases cut with
     ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ |
     ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ |
     ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩
   · have first := UpperEventEnergy11.original137_two cut sourceEq directionEq
     have small := cheap_others logged completed cheap 137 (by decide)
     omega
   · have stationary := cut.stationary_source 139 (by decide) sourceEq
     have prefixCheap := prefix_cell_cheap logged completed cut cheap 141 (by decide)
     have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [headEq] using cut.headEffect
     have survives := StationaryExit11.survives139 cut.before.logged checked effect cut.after stationary prefixCheap
     have shape : outcomes=cut.beforeOutcomes ++ .push 139 (.stay 140)::cut.afterOutcomes := by
       simpa only [headEq] using cut.outcomesEq
     have original : endGroup [139] outcomes≠[] := by rw [shape]; exact survives
     exact False.elim (survivor_absurd logged completed cheap 139 (by decide) original)
   · have stationary := cut.stationary_source 191 (by decide) sourceEq
     have prefixCheap := prefix_cell_cheap logged completed cut cheap 193 (by decide)
     have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have effect : Matches cut.middle cut.actor (.push 191 (.stay 192)) := by simpa only [headEq] using cut.headEffect
     have survives := StationaryExit11.survives191 cut.before.logged checked effect cut.after stationary prefixCheap
     have shape : outcomes=cut.beforeOutcomes ++ .push 191 (.stay 192)::cut.afterOutcomes := by
       simpa only [headEq] using cut.outcomesEq
     have original : endGroup [191] outcomes≠[] := by rw [shape]; exact survives
     exact False.elim (survivor_absurd logged completed cheap 191 (by decide) original)
   · exact False.elim (excludeReset (UpperReset11.FirstCut.after_reset cut 138 sourceEq (by simp [UpperReset11.Reset,directionEq])))
   · exact False.elim (excludeReset (UpperReset11.FirstCut.after_reset cut 138 sourceEq (by simp [UpperReset11.Reset,directionEq])))
   · exact False.elim (excludeReset (UpperReset11.FirstCut.after_reset cut 190 sourceEq (by simp [UpperReset11.Reset,directionEq])))
   · have prefixCheap := prefix_cell_cheap logged completed cut cheap 188 (by decide)
     have effect : Matches cut.middle cut.actor (.push 190 (.stay 189)) := by simpa only [headEq] using cut.headEffect
     rcases Upper190After11.FirstCut.after_190west cut sourceEq directionEq effect prefixCheap with survives | good
     · exact False.elim (survivor_absurd logged completed cheap 191 (by decide) survives)
     · have before := cut.before.logged.end_subset (by decide) Upper190After11.group (by decide) (by decide)
       have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ before.1 before.2
       have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
       have size := endGroup_length_le Upper190After11.group cut.beforeOutcomes
       change (endGroup Upper190After11.group cut.beforeOutcomes).length≤4 at size
       have bounded := Nat.le_trans (update_length (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome) size
       have beforeSubset := end_subset_selected cut.before.logged (by decide) Upper190After11.group U6
         (by decide) (by decide) (by decide) (by decide)
       have afterSubset := update_mono _ _ before.1 beforeSubset cut.headOutcome
       have future := ParkedEnergy11.future_energy afterReached cut.after completed _ nextUnique nextInside bounded good
       have bound := cap _ nextUnique afterSubset
       omega
   · have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)) := by simpa only [headEq] using cut.headEffect
     obtain ⟨selected,good⟩ := Upper216After11.FirstCut.after_216east cut sourceEq effect
     have inside : [191,217]⊆cut.actor.state.boulders := List.Subset.trans selected upperAfterInside
     have subset : [191,217]⊆nextGroup cut := List.Subset.trans selected upperAfterSubset
     obtain ⟨phase,atIndex⟩ := beforeValid.2
     have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase cut.middle atIndex
     have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
         (phaseOf soko1_1.initial.holes cut.middle) cut.middle := by rw [←phaseEq]; exact atIndex
     have activeBefore : phaseOf soko1_1.initial.holes cut.middle<16 :=
       HazardPhaseCountedCorrection.active_of_step _ _ within _ _ cut.headChecked
     have holesSame : cut.actor.state.holes=cut.middle.holes := by rw [effect.2]
     have active : phaseOf soko1_1.initial.holes cut.actor.state<16 := by
       simpa only [phaseOf,holesSame] using activeBefore
     have future := PostEnergy11.future_energy true afterReached cut.after completed active [191,217]
       (by decide) inside (by decide) good
     have bound := cap [191,217] (by decide) subset
     omega
#print axioms upper_four
end Owner1007.UpperReserve11
