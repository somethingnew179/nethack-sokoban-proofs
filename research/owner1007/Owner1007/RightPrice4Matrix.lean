import Owner1007.RightPrice4Node0
import Owner1007.RightPrice4Node1
import Owner1007.RightPrice4Node2
import Owner1007.RightPrice4Node3
import Owner1007.RightPrice4Node4
import Owner1007.RightPrice4Node5
import Owner1007.RightPrice4Node6
namespace Owner1007.RightPrice4
open NetHack.Sokoban
theorem matrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p locks region credit = true := by
  change (List.finRange 7).all matrixNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact matrix0
  · exact matrix1
  · exact matrix2
  · exact matrix3
  · exact matrix4
  · exact matrix5
  · exact matrix6
#print axioms matrix
end Owner1007.RightPrice4
