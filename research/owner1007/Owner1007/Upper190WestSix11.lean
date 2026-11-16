import Owner1007.ParkedFourSix11
import Owner1007.Upper190WordAfter11
import Owner1007.UpperCheapConsumed11
import Owner1007.HeroEnergySubset11
namespace Owner1007.Upper190WestSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 189))) :
 6≤energy soko1_1.initial final U6 outcomes := by
 by_cases enough : 6≤energy soko1_1.initial final U6 outcomes
 · exact enough
 · have cheap : energy soko1_1.initial final U6 outcomes<6 := by omega
   let group := update (endGroup Upper190After11.group cut.beforeOutcomes) cut.headOutcome
   have beforeValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have afterActual := step_boulders_nodup _ _ _ _ beforeValid.1 cut.headChecked
   have reached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have bigFacts := UpperCutBudget11.next_facts cut
   have headCost := UpperCutBudget11.head_gap cut
   have tailNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) valid
     (UpperCutBudget11.nextGroup cut) bigFacts.1 bigFacts.2.1 bigFacts.2.2
   change 0≤energy cut.actor.state final (UpperCutBudget11.nextGroup cut) cut.afterOutcomes at tailNN
   have split := energy_append soko1_1.initial cut.middle final U6 cut.beforeOutcomes
     (cut.headOutcome::cut.afterOutcomes)
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
     (endGroup U6 cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
   change energy cut.middle final (endGroup U6 cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
     charge NetHack.Soko11Hero315.holeWeight (endGroup U6 cut.beforeOutcomes) cut.headOutcome+
     value cut.actor.state (UpperCutBudget11.nextGroup cut)-value cut.middle (endGroup U6 cut.beforeOutcomes)+
     energy cut.actor.state final (UpperCutBudget11.nextGroup cut) cut.afterOutcomes at one
   have prefixCompare := energy_subset (Trace.nil soko1_1.initial) cut.before.logged
     Guard188FourWord11.G U6 (by decide) (by decide) (by decide) (by decide) (by decide)
   have prefixCheap : energy soko1_1.initial cut.middle Guard188FourWord11.G cut.beforeOutcomes<4 := by
     rw [cut.outcomesEq] at cheap
     omega
   rcases Upper190WordAfter11.after190west cut sourceEq directionEq effect prefixCheap with survives|covered|parked
   · exact False.elim (UpperSixExit11.survivor_six_absurd logged completed cheap 191 (by decide) survives)
   · obtain ⟨prefixPaid,cover⟩ := covered
     have selected := cut.before.logged.end_subset (by decide) Upper190After11.group (by decide) (by decide)
     have unique := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ selected.1 selected.2
     have inside := GhostSubset.update_subset _ _ _ cut.headEffect _ selected.1 selected.2
     have groupBound : group.length≤4 :=
       Nat.le_trans (update_length _ _) (endGroup_length_le Upper190After11.group cut.beforeOutcomes)
     have allGone := UpperCheapConsumed11.all_gone logged completed cheap
     have mono := logged.end_mono (by decide) Upper190After11.group U6 (by decide) (by decide) (by decide)
     rw [allGone] at mono
     have gone : endGroup Upper190After11.group outcomes=[] :=
       List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using mono member)
     rw [cut.outcomesEq,endGroup_append] at gone
     have groupGone : endGroup group cut.afterOutcomes=[] := gone
     have future := Upper187Cover11.future_energy reached cut.after group unique inside (by omega) cover groupGone
     have beforeInclude := end_subset_selected cut.before.logged (by decide) Upper190After11.group U6
       (by decide) (by decide) (by decide) (by decide)
     have inclusion := update_mono _ _ selected.1 beforeInclude cut.headOutcome
     have tailCompare := energy_subset reached cut.after group (UpperCutBudget11.nextGroup cut)
       unique bigFacts.1 inclusion bigFacts.2.1 bigFacts.2.2
     rw [cut.outcomesEq] at cheap
     omega
   · exact False.elim (ParkedFourSix11.absurd logged completed cut sourceEq directionEq effect cheap parked)
#print axioms upper_six
end Owner1007.Upper190WestSix11