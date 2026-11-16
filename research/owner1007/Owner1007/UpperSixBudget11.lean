import Owner1007.UpperCutBudget11
namespace Owner1007.UpperSixBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11

theorem cheap_others_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<6) :
 ∀ cell∈C, energy soko1_1.initial final [cell] outcomes<4 := by
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide) (by decide)
 change energy soko1_1.initial final U6 outcomes = _ at split
 have pair := PairBound11.pair_energy logged completed
 change 2≤energy soko1_1.initial final TightSplit11.A outcomes at pair
 have all := c_sum logged
 have a := energy_nonnegative logged [137] (by decide) (by decide)
 have b := energy_nonnegative logged [141] (by decide) (by decide)
 have c := energy_nonnegative logged [188] (by decide) (by decide)
 have d := energy_nonnegative logged [193] (by decide) (by decide)
 intro cell member
 change cell∈[137,141,188,193] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> omega

theorem prefix_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final U6 outcomes<6) (cell : Cell) (member : cell∈C) :
 energy soko1_1.initial cut.middle [cell] cut.beforeOutcomes<4 := by
 have finalCheap := cheap_others_four logged completed cheap cell member
 have all : C⊆soko1_1.initial.boulders := by decide
 have subset : [cell]⊆soko1_1.initial.boulders := by
   intro c found
   have same : c=cell := List.mem_singleton.mp found
   exact same ▸ all member
 have bound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
   [cell] (by simp) subset
 rw [←cut.outcomesEq] at bound
 omega

theorem two_tail_le {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) :
 2 + energy cut.actor.state final (nextGroup cut) cut.afterOutcomes≤energy soko1_1.initial final U6 outcomes := by
 have beforeNN := energy_nonnegative cut.before.logged U6 (by decide) (by decide)
 have one := head_gap cut
 have split := energy_append soko1_1.initial cut.middle final U6 cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have after := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup U6 cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup U6 cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes) =
   charge NetHack.Soko11Hero315.holeWeight (endGroup U6 cut.beforeOutcomes) cut.headOutcome +
    value cut.actor.state (nextGroup cut) - value cut.middle (endGroup U6 cut.beforeOutcomes) +
    energy cut.actor.state final (nextGroup cut) cut.afterOutcomes at after
 have same := congrArg (energy soko1_1.initial final U6) cut.outcomesEq
 omega

theorem six_suffices {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (upper : 6≤energy soko1_1.initial final U6 outcomes) : 325≤pushes := by
 have splitOne := Hero315Frame11.energy_split logged U6 TightSplit11.B (by decide) (by decide)
 have splitTwo := Hero315Frame11.energy_split logged (U6++TightSplit11.B) Rest (by decide) (by decide)
 have perm : soko1_1.initial.boulders.Perm ((U6++TightSplit11.B)++Rest) := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
 have total := total_energy logged completed
 have lower := LeftEnergy11.pair_energy_universal logged completed
 change 4≤energy soko1_1.initial final TightSplit11.B outcomes at lower
 have rest := energy_nonnegative logged Rest (by decide) (by decide)
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms cheap_others_four
#print axioms prefix_four
#print axioms two_tail_le
#print axioms six_suffices
end Owner1007.UpperSixBudget11
