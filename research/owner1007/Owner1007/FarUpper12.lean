import Owner1007.FarUpperNode012
import Owner1007.FarUpperNode112
import Owner1007.FarUpperNode212
namespace Owner1007.FarUpper12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem matrix_rows : ∀ i, matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2 := by omega
 rcases choices with rfl|rfl|rfl
 · exact matrix0
 · exact matrix1
 · exact matrix2
theorem classification_rows : ∀ i, classificationNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2 := by omega
 rcases choices with rfl|rfl|rfl
 · exact classification0
 · exact classification1
 · exact classification2
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by
 change (List.finRange 3).all matrixNode=true
 exact List.all_eq_true.mpr (fun i _ => matrix_rows i)
theorem classification (i : Fin 3) (hero : Cell) (heroInside : hero∈region i)
 (dir : Dir) (source : Cell) (sourceInside : source∈sources)
 (adjacent : advance soko1_2.board hero dir=some source) (pays : paid source dir) : classified i source dir := by
 have row := List.all_eq_true.mp
  (List.all_eq_true.mp (List.all_eq_true.mp (classification_rows i) hero heroInside)
   dir (Geometry.all_directions dir)) source sourceInside
 exact of_decide_eq_true row adjacent pays
#print axioms matrix
#print axioms classification
end Owner1007.FarUpper12


