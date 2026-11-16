import Owner1007.Cage10MatrixNode0
import Owner1007.Cage10MatrixNode1
import Owner1007.Cage10MatrixNode2
import Owner1007.Cage10MatrixNode3
import Owner1007.Cage10MatrixNode4
import Owner1007.Cage10MatrixNode5
import Owner1007.Cage10MatrixNode6
import Owner1007.Cage10MatrixNode7
import Owner1007.Cage10MatrixNode8
import Owner1007.Cage10MatrixNode9
import Owner1007.Cage10ClassNode0
import Owner1007.Cage10ClassNode1
import Owner1007.Cage10ClassNode2
import Owner1007.Cage10ClassNode3
import Owner1007.Cage10ClassNode4
import Owner1007.Cage10ClassNode5
import Owner1007.Cage10ClassNode6
import Owner1007.Cage10ClassNode7
namespace Owner1007.Cage10
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem matrix_rows : ∀ i, matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6∨v=7∨v=8∨v=9 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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

theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by
 change (List.finRange 10).all matrixNode=true
 exact List.all_eq_true.mpr (fun i _ => matrix_rows i)


theorem classification_rows : ∀ i, classificationNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6∨v=7 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact classification0
 · exact classification1
 · exact classification2
 · exact classification3
 · exact classification4
 · exact classification5
 · exact classification6
 · exact classification7

theorem classification (i : Fin 8) (hero : Cell) (heroInside : hero∈region (basic i))
 (dir : Dir) (source : Cell) (sourceInside : source∈paidSources)
 (adjacent : advance soko1_2.board hero dir=some source) (pays : paid source dir) :
 classified (basic i) source dir := by
 have row := List.all_eq_true.mp
   (List.all_eq_true.mp (List.all_eq_true.mp (classification_rows i) hero heroInside)
     dir (Geometry.all_directions dir)) source sourceInside
 exact of_decide_eq_true row adjacent pays


#print axioms matrix
#print axioms classification
end Owner1007.Cage10

