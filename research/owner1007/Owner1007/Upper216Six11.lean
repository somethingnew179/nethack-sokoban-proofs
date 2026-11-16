import Owner1007.UpperSixBudget11
import Owner1007.Upper216After11
import Owner1007.StationaryGuardsSix11
import Owner1007.RightFour11
namespace Owner1007.Upper216Six11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

theorem reserve_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 216)
 (headEq : cut.headOutcome=.push 216 (.stay 217)) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)) := by
     simpa only [headEq] using cut.headEffect
   obtain ⟨selected,_⟩ := Upper216After11.FirstCut.after_216east cut sourceEq effect
   have before191 : 191∈endGroup originalGroup cut.beforeOutcomes := by
     have found := selected (show 191∈([191,217] : List Cell) by simp)
     rw [headEq] at found
     simp only [update,move,post] at found
     split at found
     · exact List.mem_of_mem_erase (List.mem_cons.mp found |>.resolve_left (by decide))
     · exact found
   have stationary := cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
     original_good (by simp) 191 (by simp) before191
   have prefixCheap := UpperSixBudget11.prefix_four logged completed cut cheap 193 (by decide)
   have guarded := StationaryGuardsSix11.guard193 cut.before.logged stationary (by omega)
   have beforeGuard := cut.before.logged.end_subset (by decide) [193] (by decide) (by decide)
   have blocker : 193∈cut.actor.state.boulders ∨ 192∈cut.actor.state.boulders := by
     have shape : cut.actor.state.boulders=217::cut.middle.boulders.erase 216 := by rw [effect.2]
     rw [shape]
     rcases guarded with normal | shifted
     · left
       exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 193≠216)).mpr
         (beforeGuard.2 (by rw [normal]; simp)))
     · right
       exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 192≠216)).mpr
         (beforeGuard.2 (by rw [shifted]; simp)))
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have afterReached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have upperBefore := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
   have upperAfterInside := GhostSubset.update_subset _ _ _ cut.headEffect _ upperBefore.1 upperBefore.2
   have upperBeforeSubset := end_subset_selected cut.before.logged (by decide) originalGroup U6
     (by decide) (by decide) (by decide) (by decide)
   have upperAfterSubset := update_mono _ _ upperBefore.1 upperBeforeSubset cut.headOutcome
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
   have hero : cut.actor.state.player=216 := by rw [effect.2]
   have future := RightFour11.future_four afterReached cut.after completed active hero inside blocker
   have facts := next_facts cut
   have bound := energy_subset afterReached cut.after [191,217] (nextGroup cut) (by decide) facts.1 subset facts.2.1 facts.2.2
   have sum := UpperSixBudget11.two_tail_le cut
   omega
#print axioms reserve_six
end Owner1007.Upper216Six11
