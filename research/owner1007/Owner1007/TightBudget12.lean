import Owner1007.TokenCounting
import Owner1007.PriceTrap12

namespace Owner1007.TightBudget12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds Owner1007.TokenAccounting
def ordinary : List Cell := [108,158,159,186,187,210,213,237,238,263,265]
def left : List Cell := ordinary ++ [318,371]

theorem ordinary_debt (cell : Cell) (member : cell ∈ ordinary) :
    7 ≤ -Generated.soko1_2Potential.boulder cell := by
  have all : ∀ c ∈ ordinary, 7 ≤ -Generated.soko1_2Potential.boulder c := by decide +kernel
  exact all cell member

theorem ordinary_consumed_of_left_energy_le_five
    {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
    (small : energy Generated.soko1_2Potential left outcomes ≤ 5) :
    ∀ cell ∈ ordinary, endGroup [cell] outcomes = [] := by
  intro cell member
  by_cases gone : endGroup [cell] outcomes = []
  · exact gone
  · have belongs : cell ∈ left := List.mem_append_left _ member
    have bound := logged.member_energy_le Generated.soko1_2_potential_valid
      (show soko1_2.initial.boulders.Nodup by decide +kernel) left
      (show left.Nodup by decide +kernel)
      (show left ⊆ soko1_2.initial.boulders by decide +kernel) cell belongs
    have ledger := survivor_energy Generated.soko1_2Potential cell outcomes gone
    have debt := ordinary_debt cell member
    simp only [Int.ofNat_eq_natCast] at ledger
    omega

#print axioms ordinary_consumed_of_left_energy_le_five
end Owner1007.TightBudget12
