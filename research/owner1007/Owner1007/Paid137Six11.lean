import Owner1007.PairReserveBudget11
import Owner1007.PairHeadCases11
import Owner1007.PairPost11
import Owner1007.Pair190After11
import Owner1007.ParkedThree11
import Owner1007.Pair13711
import Owner1007.Pair137Energy11
import Owner1007.PairResetFuture11
import Owner1007.UpperSixExit11
import Owner1007.StationaryExit11
import Owner1007.PostEnergy11
namespace Owner1007.Paid137Six11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11 Owner1007.PairReserveBudget11
open NetHack.Sokoban.HazardPhaseCountedCorrection (phaseOf)

theorem active_after_stay {dirs final pushes moves outcomes source landing}
 (cut : PairReserveBudget11.Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes))
 (effect : Matches cut.middle cut.actor (.push source (.stay landing))) :
 phaseOf soko1_1.initial.holes cut.actor.state<16 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 obtain ⟨phase,atIndex⟩ := valid.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase cut.middle atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
     (phaseOf soko1_1.initial.holes cut.middle) cut.middle := by rw [←phaseEq]; exact atIndex
 have beforeActive : phaseOf soko1_1.initial.holes cut.middle<16 :=
   HazardPhaseCountedCorrection.active_of_step _ _ within _ _ cut.headChecked
 have holesSame : cut.actor.state.holes=cut.middle.holes := by rw [effect.2]
 simpa only [phaseOf,holesSame] using beforeActive

theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (paid137 : 2≤energy soko1_1.initial final [137] outcomes) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   have cheapG := group_cheap logged cheap paid137
   have others := others_cheap logged completed cheap paid137
   have cheapA := pair_cheap logged cheapG
   obtain ⟨cut⟩ := PairFirstCut11.first_cut logged completed cheapA
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have afterReached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have facts := next_facts cut
   have afterCheap := suffix_cheap cut cheapG
   have cap : ∀ small : List Cell, small.Nodup → small⊆nextGroup cut →
       energy cut.actor.state final small cut.afterOutcomes<2 := by
     intro small unique subset
     have bound := energy_subset afterReached cut.after small (nextGroup cut) unique facts.1 subset facts.2.1 (by omega)
     omega
   have beforeA := cut.before.logged.end_subset (by decide) PairFirstCut11.originalGroup (by decide) (by decide)
   have afterA := GhostSubset.update_subset _ _ _ cut.headEffect _ beforeA.1 beforeA.2
   have beforeInclude := end_subset_selected cut.before.logged (by decide) PairFirstCut11.originalGroup G
     (by decide) (by decide) (by decide) (by decide)
   have afterInclude := update_mono _ _ beforeA.1 beforeInclude cut.headOutcome
   have post_subset : ∀ cells : List Cell,
       (update (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.headOutcome).Perm cells →
       cells⊆cut.actor.state.boulders ∧ cells⊆nextGroup cut := by
     intro cells perm
     exact ⟨fun _ found => afterA (perm.mem_iff.mpr found),
       fun _ found => afterInclude (perm.mem_iff.mpr found)⟩
   have source_owned : ∀ cell, cut.actor.pushSource=some cell →
       cell∈endGroup PairFirstCut11.originalGroup cut.beforeOutcomes := by
     intro cell sourceEq
     obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
     have same : source=cell := Option.some.inj (metadata.symm.trans sourceEq)
     exact same ▸ owner
   rcases PairHeadCases11.head_cases cut with
     ⟨directionEq,sourceEq,headEq⟩|⟨directionEq,sourceEq,headEq⟩|⟨directionEq,sourceEq,headEq⟩|
     ⟨directionEq,sourceEq,headEq⟩|⟨directionEq,sourceEq,headEq⟩|⟨directionEq,sourceEq,headEq⟩|
     ⟨directionEq,sourceEq,headEq⟩|⟨directionEq,sourceEq,headEq⟩
   · have stationary := PairFirstCut11.stationary_source cut 139 (by decide) (source_owned 139 sourceEq)
     have prefixCheap := prefix_cheap cut 141 (by decide) (others 141 (by decide))
     have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [headEq] using cut.headEffect
     have survives := StationaryExit11.survives139 cut.before.logged checked effect cut.after stationary prefixCheap
     have full : endGroup [139] outcomes≠[] := by rw [cut.outcomesEq,headEq]; exact survives
     exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 139 (by decide) full)
   · have stationary := PairFirstCut11.stationary_source cut 191 (by decide) (source_owned 191 sourceEq)
     have prefixCheap := prefix_cheap cut 193 (by decide) (others 193 (by decide))
     have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
     have effect : Matches cut.middle cut.actor (.push 191 (.stay 192)) := by simpa only [headEq] using cut.headEffect
     have survives := StationaryExit11.survives191 cut.before.logged checked effect cut.after stationary prefixCheap
     have full : endGroup [191] outcomes≠[] := by rw [cut.outcomesEq,headEq]; exact survives
     exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 191 (by decide) full)
   · have effect : Matches cut.middle cut.actor (.push 190 (.stay 191)) := by simpa only [headEq] using cut.headEffect
     have perm := PairPost11.before_after (support:=189) (source:=190) (landing:=191) (dir:=.east)
       (old:=[139,190]) (next:=[139,191]) cut (by simp [PairPost11.edges]) sourceEq directionEq effect
     obtain ⟨inside,subset⟩ := post_subset _ perm.2
     have hero : cut.actor.state.player=190 := by rw [effect.2]
     have active := active_after_stay cut effect
     have future := PairResetFuture11.future_two afterReached cut.after completed active (by rw [hero]; decide) inside
     have bound := cap [139,191] (by decide) subset
     omega
   · have prefixCheap := prefix_cheap cut 188 (by decide) (others 188 (by decide))
     have effect : Matches cut.middle cut.actor (.push 190 (.stay 189)) := by simpa only [headEq] using cut.headEffect
     rcases Pair190After11.after_190west cut sourceEq directionEq effect prefixCheap with survives|good
     · exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 191 (by decide) survives)
     · change OwnedCorral11.Good ParkedThree11.locks ParkedThree11.region cut.actor.state (nextGroup cut) at good
       have future := ParkedThree11.future_energy afterReached cut.after completed (nextGroup cut) facts.1 facts.2.1 facts.2.2 good
       omega
   · have effect : Matches cut.middle cut.actor (.push 138 (.stay 139)) := by simpa only [headEq] using cut.headEffect
     have perm := PairPost11.before_after (support:=137) (source:=138) (landing:=139) (dir:=.east)
       (old:=[138,191]) (next:=[139,191]) cut (by simp [PairPost11.edges]) sourceEq directionEq effect
     obtain ⟨inside,subset⟩ := post_subset _ perm.2
     have hero : cut.actor.state.player=138 := by rw [effect.2]
     have active := active_after_stay cut effect
     have future := PairResetFuture11.future_two afterReached cut.after completed active (by rw [hero]; decide) inside
     have bound := cap [139,191] (by decide) subset
     omega
   · have effect : Matches cut.middle cut.actor (.push 138 (.stay 137)) := by simpa only [headEq] using cut.headEffect
     have perm := PairPost11.before_after (support:=139) (source:=138) (landing:=137) (dir:=.west)
       (old:=[138,191]) (next:=[137,191]) cut (by simp [PairPost11.edges]) sourceEq directionEq effect
     obtain ⟨inside,subset⟩ := post_subset _ perm.2
     have hero : cut.actor.state.player=138 := by rw [effect.2]
     have active := active_after_stay cut effect
     have future := Pair137Energy11.future_two_of_closed Pair13711.closed afterReached cut.after completed active hero inside
     have bound := cap [137,191] (by decide) subset
     omega
   · have effect : Matches cut.middle cut.actor (.push 112 (.stay 113)) := by simpa only [headEq] using cut.headEffect
     have perm := PairPost11.before_after (support:=111) (source:=112) (landing:=113) (dir:=.east)
       (old:=[139,112]) (next:=[139,113]) cut (by simp [PairPost11.edges]) sourceEq directionEq effect
     obtain ⟨inside,subset⟩ := post_subset _ perm.2
     have hero : cut.actor.state.player=112 := by rw [effect.2]
     have active := active_after_stay cut effect
     have good : OwnedCorral11.Good (PostEnergy11.locks false) (PostEnergy11.region false) cut.actor.state [139,113] := by
       refine ⟨0,?_,?_⟩
       · rw [hero]; decide +kernel
       · decide
     have future := PostEnergy11.future_energy false afterReached cut.after completed active [139,113]
       (by decide) inside (by decide) good
     have bound := cap [139,113] (by decide) subset
     omega
   · have effect : Matches cut.middle cut.actor (.push 216 (.stay 217)) := by simpa only [headEq] using cut.headEffect
     have perm := PairPost11.before_after (support:=215) (source:=216) (landing:=217) (dir:=.east)
       (old:=[216,191]) (next:=[191,217]) cut (by simp [PairPost11.edges]) sourceEq directionEq effect
     obtain ⟨inside,subset⟩ := post_subset _ perm.2
     have hero : cut.actor.state.player=216 := by rw [effect.2]
     have active := active_after_stay cut effect
     have good : OwnedCorral11.Good (PostEnergy11.locks true) (PostEnergy11.region true) cut.actor.state [191,217] := by
       refine ⟨0,?_,?_⟩
       · rw [hero]; decide +kernel
       · decide
     have future := PostEnergy11.future_energy true afterReached cut.after completed active [191,217]
       (by decide) inside (by decide) good
     have bound := cap [191,217] (by decide) subset
     omega

#print axioms upper_six
end Owner1007.Paid137Six11
