import Owner1007.UpperCutBudget11
namespace Owner1007.UpperEventEnergy11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

theorem event_gap_le {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆soko1_1.initial.boulders) :
 charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome +
   value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome) -
   value cut.middle (endGroup group cut.beforeOutcomes) ≤ energy soko1_1.initial final group outcomes := by
 have prefixNN := energy_nonnegative cut.before.logged group unique inside
 have before := cut.before.logged.end_subset (by decide) group unique inside
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have afterValid := (groupCertificate 18).preserved _ _ _ valid cut.headChecked
 have actual := step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
 have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect actual _ before.1 before.2
 have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have groupBound := List.Nodup.length_le_of_subset unique inside
 change group.length≤18 at groupBound
 have beforeBound := endGroup_length_le group cut.beforeOutcomes
 have afterBound := update_length (endGroup group cut.beforeOutcomes) cut.headOutcome
 have afterNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 18) afterValid
   _ nextUnique nextInside (by omega)
 change 0≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at afterNN
 have split := energy_append soko1_1.initial cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes) =
   charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome +
    value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome) -
    value cut.middle (endGroup group cut.beforeOutcomes) +
    energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same := congrArg (energy soko1_1.initial final group) cut.outcomesEq
 omega

theorem original137_two {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 137) (directionEq : cut.direction=.west) :
 2≤energy soko1_1.initial final [137] outcomes := by
 have stationary := cut.stationary_source 137 (by simp) sourceEq
 have prior := no_push_unchanged [137] cut.beforeOutcomes stationary
 have before := cut.before.logged.end_subset (by decide) [137] (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have row := CutStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect before.1 before.2
   ⟨137,by rw [prior]; simp,sourceEq,by rw [directionEq]; simp [CutActor11.Exit]⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [137] cut.beforeOutcomes) cut.headOutcome +
   value cut.actor.state (update (endGroup [137] cut.beforeOutcomes) cut.headOutcome) -
   value cut.middle (endGroup [137] cut.beforeOutcomes) at row
 have bound := event_gap_le cut [137] (by decide) (by decide)
 omega
#print axioms event_gap_le
#print axioms original137_two
end Owner1007.UpperEventEnergy11
