import Owner1007.AfterJ12Node0_0
import Owner1007.AfterJ12Node0_1
import Owner1007.AfterJ12Node0_2
import Owner1007.AfterJ12Node0_3
import Owner1007.AfterJ12Node0_4
namespace Owner1007.AfterJ12
open NetHack.Sokoban
open Owner1007
theorem matrix210 : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes (locks 0) (region 0) (paid 0) = true := by
 change (List.finRange 5).all (nodeCheck 0)=true
 apply List.all_eq_true.mpr
 intro i _
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl
 · exact node0_0
 · exact node0_1
 · exact node0_2
 · exact node0_3
 · exact node0_4
#print axioms matrix210
end Owner1007.AfterJ12
