import Owner1007.RightEntrySevenNode012
import Owner1007.RightEntrySevenNode112
import Owner1007.RightEntrySevenNode212
import Owner1007.RightEntrySevenNode312
namespace Owner1007.RightEntrySeven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem matrix_rows : ∀ i,matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices:v=0∨v=1∨v=2∨v=3:=by omega
 rcases choices with rfl|rfl|rfl|rfl
 · exact matrix0
 · exact matrix1
 · exact matrix2
 · exact matrix3
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by
 change (List.finRange 4).all matrixNode=true
 exact List.all_eq_true.mpr (fun i _=>matrix_rows i)
#print axioms matrix
#print axioms head_classification
end Owner1007.RightEntrySeven12
