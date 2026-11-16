import Owner1007.After238210Node0
import Owner1007.After238210Node1
import Owner1007.After238210Node2
import Owner1007.After238210Node3
import Owner1007.After238210Node4
namespace Owner1007.After23821012
open NetHack.Sokoban
open Owner1007
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by
 unfold PricedCorral11.checkExcept
 apply List.all_eq_true.mpr
 intro i member
 change nodeCheck i=true
 obtain ⟨v,h⟩ := i
 have cases : v=0∨v=1∨v=2∨v=3∨v=4 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl
 · exact node0
 · exact node1
 · exact node2
 · exact node3
 · exact node4

#print axioms matrix
end Owner1007.After23821012

