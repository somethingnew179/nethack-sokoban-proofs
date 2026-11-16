import Owner1007.UpperBudget11
import Owner1007.HeroEndSubset11
import Owner1007.UpperFirstCut11
import Owner1007.CutEnergy11
namespace Owner1007.UpperCutBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11

def nextGroup {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) : List Cell :=
 update (endGroup U6 cut.beforeOutcomes) cut.headOutcome

theorem next_facts {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) :
 (nextGroup cut).Nodup ∧ nextGroup cut⊆cut.actor.state.boulders ∧ (nextGroup cut).length≤18 := by
 have before := cut.before.logged.end_subset (by decide) U6 (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have actual := step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
 have unq := GhostSubset.update_unique _ _ _ cut.headEffect actual _ before.1 before.2
 have inside := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have bounded := endGroup_length_le U6 cut.beforeOutcomes
 change (endGroup U6 cut.beforeOutcomes).length≤6 at bounded
 have nextSize := update_length (endGroup U6 cut.beforeOutcomes) cut.headOutcome
 exact ⟨unq,inside,by change (update (endGroup U6 cut.beforeOutcomes) cut.headOutcome).length≤18; omega⟩

theorem head_gap {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) :
 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup U6 cut.beforeOutcomes) cut.headOutcome +
   value cut.actor.state (nextGroup cut) - value cut.middle (endGroup U6 cut.beforeOutcomes) := by
 have before := cut.before.logged.end_subset (by decide) U6 (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have included := end_subset_selected cut.before.logged (by decide) originalGroup U6
   (by decide) (by decide) (by decide) (by decide)
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 exact CutStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect before.1 before.2
   ⟨source,included owner,metadata,CutEnergy11.upper_paid source cut.direction pays⟩

theorem suffix_cheap {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final U6 outcomes<4) :
 energy cut.actor.state final (nextGroup cut) cut.afterOutcomes<2 := by
 have beforeNN := energy_nonnegative cut.before.logged U6 (by decide) (by decide)
 have one := head_gap cut
 have split := energy_append soko1_1.initial cut.middle final U6 cut.beforeOutcomes
   (cut.headOutcome::cut.afterOutcomes)
 have after := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup U6 cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup U6 cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes) =
   charge NetHack.Soko11Hero315.holeWeight (endGroup U6 cut.beforeOutcomes) cut.headOutcome +
    value cut.actor.state (nextGroup cut) - value cut.middle (endGroup U6 cut.beforeOutcomes) +
    energy cut.actor.state final (nextGroup cut) cut.afterOutcomes at after
 rw [cut.outcomesEq] at cheap
 omega

theorem prefix_cell_cheap {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final U6 outcomes<4) (cell : Cell) (member : cell∈C) :
 energy soko1_1.initial cut.middle [cell] cut.beforeOutcomes<2 := by
 have finalCheap := cheap_others logged completed cheap cell member
 have all : C⊆soko1_1.initial.boulders := by decide
 have subset : [cell]⊆soko1_1.initial.boulders := by
   intro c found
   have same : c=cell := List.mem_singleton.mp found
   exact same ▸ all member
 have bound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
   [cell] (by simp) subset
 rw [←cut.outcomesEq] at bound
 omega

theorem survivor_absurd {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : energy soko1_1.initial final U6 outcomes<4) (cell : Cell) (member : cell∈[139,191])
 (survives : endGroup [cell] outcomes≠[]) : False := by
 have subset : [cell]⊆U6 := by
   rcases List.mem_cons.mp member with rfl|later
   · decide
   · have same : cell=191 := List.mem_singleton.mp later
     subst cell; decide
 have bound := energy_subset (Trace.nil soko1_1.initial) logged [cell] U6 (by simp) (by decide)
   subset (by decide) (by decide)
 have ledger := survivor_energy logged completed cell survives
 have debt : value soko1_1.initial [cell]≤-4 := by
   rcases List.mem_cons.mp member with rfl|later
   · decide +kernel
   · have same : cell=191 := List.mem_singleton.mp later
     subst cell; decide +kernel
 have nonnegative : (0:Int)≤Int.ofNat (ownPushes [cell] outcomes) := Int.ofNat_nonneg _
 omega

#print axioms head_gap
#print axioms suffix_cheap
#print axioms prefix_cell_cheap
#print axioms survivor_absurd
end Owner1007.UpperCutBudget11
