import Owner1007.Cage239RetainedNode012
import Owner1007.Cage239RetainedNode112
import Owner1007.Cage239RetainedNode212
import Owner1007.Cage239RetainedNode312
import Owner1007.Cage239RetainedNode412
import Owner1007.Cage239RetainedNode512
namespace Owner1007.Cage239RetainedNine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem matrix_rows : ∀ i,matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices:v=0∨v=1∨v=2∨v=3∨v=4∨v=5:=by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
 · exact matrix0
 · exact matrix1
 · exact matrix2
 · exact matrix3
 · exact matrix4
 · exact matrix5
theorem class_rows : ∀ i,classificationNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices:v=0∨v=1∨v=2∨v=3:=by omega
 rcases choices with rfl|rfl|rfl|rfl
 · exact class0
 · exact class1
 · exact class2
 · exact class3
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by
 change (List.finRange 6).all matrixNode=true
 exact List.all_eq_true.mpr (fun i _ => matrix_rows i)
theorem classification (i:Fin 4) (hero:Cell) (heroInside:hero∈region (basic i))
 (dir:Dir) (source:Cell) (sourceInside:source∈Cage23912.paidSources)
 (adjacent:advance soko1_2.board hero dir=some source) (pays:paid source dir):classified (basic i) source dir := by
 have row:=List.all_eq_true.mp
  (List.all_eq_true.mp (List.all_eq_true.mp (class_rows i) hero heroInside) dir (Geometry.all_directions dir)) source sourceInside
 exact of_decide_eq_true row adjacent pays
end Owner1007.Cage239RetainedNine12
