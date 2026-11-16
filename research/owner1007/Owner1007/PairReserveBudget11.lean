import Owner1007.PairFirstCut11
import Owner1007.UpperSixBudget11
namespace Owner1007.PairReserveBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := PairFirstCut11.originalGroup++[188]
abbrev Cut {dirs final pushes moves outcomes} :=
 UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs final pushes moves outcomes

theorem group_cheap {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final U6 outcomes<6)
 (paid137 : 2≤energy soko1_1.initial final [137] outcomes) :
 energy soko1_1.initial final G outcomes<4 := by
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide) (by decide)
 change energy soko1_1.initial final U6 outcomes=_ at split
 have all := c_sum logged
 have localSplit := Hero315Frame11.energy_split logged PairFirstCut11.originalGroup [188] (by decide) (by decide)
 change energy soko1_1.initial final G outcomes =
   energy soko1_1.initial final TightSplit11.A outcomes + energy soko1_1.initial final [188] outcomes at localSplit
 have nn141 := energy_nonnegative logged [141] (by decide) (by decide)
 have nn193 := energy_nonnegative logged [193] (by decide) (by decide)
 omega

theorem others_cheap {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : energy soko1_1.initial final U6 outcomes<6)
 (paid137 : 2≤energy soko1_1.initial final [137] outcomes) :
 ∀cell∈([141,188,193] : List Cell), energy soko1_1.initial final [cell] outcomes<2 := by
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide) (by decide)
 change energy soko1_1.initial final U6 outcomes=_ at split
 have all := c_sum logged
 have pair := PairBound11.pair_energy logged completed
 change 2≤energy soko1_1.initial final TightSplit11.A outcomes at pair
 have a := energy_nonnegative logged [141] (by decide) (by decide)
 have b := energy_nonnegative logged [188] (by decide) (by decide)
 have c := energy_nonnegative logged [193] (by decide) (by decide)
 intro cell member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl <;> omega

theorem pair_cheap {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final G outcomes<4) :
 energy soko1_1.initial final PairFirstCut11.originalGroup outcomes<4 := by
 have bound := energy_subset (Trace.nil soko1_1.initial) logged PairFirstCut11.originalGroup G
   (by decide) (by decide) (by decide) (by decide) (by decide)
 omega

def nextGroup {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes)) : List Cell :=
 update (endGroup G cut.beforeOutcomes) cut.headOutcome

theorem next_facts {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes)) :
 (nextGroup cut).Nodup ∧ nextGroup cut⊆cut.actor.state.boulders ∧ (nextGroup cut).length≤3 := by
 have before := cut.before.logged.end_subset (by decide) G (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have actual := step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
 have unq := GhostSubset.update_unique _ _ _ cut.headEffect actual _ before.1 before.2
 have inside := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have bound := endGroup_length_le G cut.beforeOutcomes
 have size := update_length (endGroup G cut.beforeOutcomes) cut.headOutcome
 exact ⟨unq,inside,by change (update (endGroup G cut.beforeOutcomes) cut.headOutcome).length≤3; change (endGroup G cut.beforeOutcomes).length≤3 at bound; omega⟩

theorem suffix_cheap {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes))
 (cheap : energy soko1_1.initial final G outcomes<4) :
 energy cut.actor.state final (nextGroup cut) cut.afterOutcomes<2 := by
 have beforeNN := energy_nonnegative cut.before.logged G (by decide) (by decide)
 have before := cut.before.logged.end_subset (by decide) G (by decide) (by decide)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have included := end_subset_selected cut.before.logged (by decide) PairFirstCut11.originalGroup G
   (by decide) (by decide) (by decide) (by decide)
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have one := PairStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect before.1 before.2
   ⟨source,included owner,metadata,pays⟩
 have split := energy_append soko1_1.initial cut.middle final G cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have after := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup G cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup G cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes) =
   charge NetHack.Soko11Hero315.holeWeight (endGroup G cut.beforeOutcomes) cut.headOutcome +
   value cut.actor.state (nextGroup cut)-value cut.middle (endGroup G cut.beforeOutcomes)+
   energy cut.actor.state final (nextGroup cut) cut.afterOutcomes at after
 rw [cut.outcomesEq] at cheap
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup G cut.beforeOutcomes) cut.headOutcome +
   value cut.actor.state (nextGroup cut)-value cut.middle (endGroup G cut.beforeOutcomes) at one
 omega

theorem prefix_cheap {dirs final pushes moves outcomes}
 (cut : Cut (dirs:=dirs) (final:=final) (pushes:=pushes) (moves:=moves) (outcomes:=outcomes))
 (cell : Cell) (member : cell∈[141,188,193])
 (cheap : energy soko1_1.initial final [cell] outcomes<2) :
 energy soko1_1.initial cut.middle [cell] cut.beforeOutcomes<2 := by
 have all : ([141,188,193] : List Cell)⊆soko1_1.initial.boulders := by decide
 have inside : [cell]⊆soko1_1.initial.boulders := by
   intro c found
   have same : c=cell := List.mem_singleton.mp found
   exact same ▸ all member
 have bound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
   [cell] (by simp) inside
 rw [←cut.outcomesEq] at bound
 omega
#print axioms group_cheap
#print axioms others_cheap
#print axioms suffix_cheap
end Owner1007.PairReserveBudget11
