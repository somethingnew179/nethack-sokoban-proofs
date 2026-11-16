import Owner1007.UpperCutBudget11
namespace Owner1007.UpperEightBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.UpperCutBudget11

theorem cheap_others_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<8) :
 ∀ cell∈C, energy soko1_1.initial final [cell] outcomes<6 := by
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

theorem prefix_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (cheap : energy soko1_1.initial final U6 outcomes<8) (cell : Cell) (member : cell∈C) :
 energy soko1_1.initial cut.middle [cell] cut.beforeOutcomes<6 := by
 have finalCheap := cheap_others_six logged completed cheap cell member
 have all : C⊆soko1_1.initial.boulders := by decide
 have subset : [cell]⊆soko1_1.initial.boulders := by
   intro c found
   have same : c=cell := List.mem_singleton.mp found
   exact same ▸ all member
 have bound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
   [cell] (by simp) subset
 rw [←cut.outcomesEq] at bound
 omega

#print axioms cheap_others_six
#print axioms prefix_six
end Owner1007.UpperEightBudget11
