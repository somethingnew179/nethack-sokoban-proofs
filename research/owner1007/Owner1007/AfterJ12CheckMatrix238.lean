import Owner1007.AfterJ12Node1_0
import Owner1007.AfterJ12Node1_1
import Owner1007.AfterJ12Node1_2
import Owner1007.AfterJ12Node1_3
import Owner1007.AfterJ12Node1_4
namespace Owner1007.AfterJ12
open NetHack.Sokoban
open Owner1007
theorem matrix238 : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes (locks 1) (region 1) (paid 1) = true := by
 change (List.finRange 5).all (nodeCheck 1)=true
 apply List.all_eq_true.mpr
 intro i _
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl
 · exact node1_0
 · exact node1_1
 · exact node1_2
 · exact node1_3
 · exact node1_4
#print axioms matrix238
end Owner1007.AfterJ12
