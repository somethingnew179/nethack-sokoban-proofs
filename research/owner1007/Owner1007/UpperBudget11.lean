import Owner1007.TightSplit11
namespace Owner1007.UpperBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def C : List Cell := [137,141,188,193]
def U6 : List Cell := TightSplit11.A ++ C
def Rest : List Cell := [133,135,264,266,268,293,315,317,321,367]

theorem c_sum {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) :
 energy soko1_1.initial final C outcomes = energy soko1_1.initial final [137] outcomes +
   energy soko1_1.initial final [141] outcomes + energy soko1_1.initial final [188] outcomes +
   energy soko1_1.initial final [193] outcomes := by
 have a := Hero315Frame11.energy_split logged [137] [141,188,193] (by decide +kernel) (by decide +kernel)
 have b := Hero315Frame11.energy_split logged [141] [188,193] (by decide +kernel) (by decide +kernel)
 have c := Hero315Frame11.energy_split logged [188] [193] (by decide +kernel) (by decide +kernel)
 change energy soko1_1.initial final C outcomes = _ at a
 simp only [List.cons_append,List.nil_append] at b c
 omega

theorem cheap_others {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final U6 outcomes<4) :
 ∀ cell∈C, energy soko1_1.initial final [cell] outcomes<2 := by
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide +kernel) (by decide +kernel)
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

/-- The only missing ingredient is a universal4 reserve for the six upper identities. -/
theorem upper_suffices {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (upper : 4≤energy soko1_1.initial final U6 outcomes) : 323≤pushes := by
 have splitOne := Hero315Frame11.energy_split logged U6 TightSplit11.B (by decide +kernel) (by decide +kernel)
 have splitTwo := Hero315Frame11.energy_split logged (U6++TightSplit11.B) Rest (by decide +kernel) (by decide +kernel)
 have perm : soko1_1.initial.boulders.Perm ((U6++TightSplit11.B)++Rest) := by decide +kernel
 have same := Hero315Frame11.energy_perm perm soko1_1.initial final outcomes
 have total := total_energy logged completed
 have lower := LeftEnergy11.pair_energy_universal logged completed
 change 4≤energy soko1_1.initial final TightSplit11.B outcomes at lower
 have rest := energy_nonnegative logged Rest (by decide +kernel) (by decide +kernel)
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms cheap_others
#print axioms upper_suffices
end Owner1007.UpperBudget11
