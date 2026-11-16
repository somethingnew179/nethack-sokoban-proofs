import Owner1007.BottomCut12Node0
import Owner1007.BottomCut12Node1
import Owner1007.BottomCut12Node2
import Owner1007.BottomCut12Node3
import Owner1007.BottomCut12Node4
import Owner1007.BottomCut12Node5
import Owner1007.BottomCut12Node6
import Owner1007.BottomCut12Node7
import Owner1007.BottomCut12Node8
import Owner1007.BottomCut12Node9
import Owner1007.BottomCut12Node10
namespace Owner1007.BottomCut12
open NetHack.Sokoban
theorem matrix : PricedCorral.check soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential locks region credit = true := by
  change (List.finRange 11).all matrixNode = true
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact matrix0
  · exact matrix1
  · exact matrix2
  · exact matrix3
  · exact matrix4
  · exact matrix5
  · exact matrix6
  · exact matrix7
  · exact matrix8
  · exact matrix9
  · exact matrix10
#print axioms matrix
end Owner1007.BottomCut12
