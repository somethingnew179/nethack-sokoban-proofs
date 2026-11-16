import Owner1007.UpperAfter187Node0
import Owner1007.UpperAfter187Node1
import Owner1007.UpperAfter187Node2
import Owner1007.UpperAfter187Node3
import Owner1007.UpperAfter187Node4
import Owner1007.UpperAfter187Node5
import Owner1007.UpperAfter187Node6
import Owner1007.UpperAfter187Node7
import Owner1007.UpperAfter187Node8
import Owner1007.UpperAfter187Node9
import Owner1007.UpperAfter187Node10
namespace Owner1007.UpperAfter18712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem matrix_rows : ∀ i, matrixNode i=true := by
 intro i
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6∨v=7∨v=8∨v=9∨v=10 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
theorem matrix : PricedCorral.check soko1_2.board soko1_2.initial.holes p locks region credit=true := by
 change (List.finRange 11).all matrixNode=true
 exact List.all_eq_true.mpr (fun i _ => matrix_rows i)
#print axioms matrix
end Owner1007.UpperAfter18712

