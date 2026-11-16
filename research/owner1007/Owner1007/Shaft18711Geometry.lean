import Owner1007.Shaft18711Data
namespace Owner1007.Shaft18711
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem geometry_node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (0:Fin 6)=true := by decide +kernel
theorem geometry_node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (1:Fin 6)=true := by decide +kernel
theorem geometry_node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (2:Fin 6)=true := by decide +kernel
theorem geometry_node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (3:Fin 6)=true := by decide +kernel
theorem geometry_node4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (4:Fin 6)=true := by decide +kernel
theorem geometry_node5 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (5:Fin 6)=true := by decide +kernel
theorem geometry_checked (i : Fin 6) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨v,bound⟩ := i
 have choices : v=0∨v=1∨v=2∨v=3∨v=4∨v=5 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl
 · exact geometry_node0
 · exact geometry_node1
 · exact geometry_node2
 · exact geometry_node3
 · exact geometry_node4
 · exact geometry_node5
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor geometry_checked
#print axioms geometry_checked
#print axioms closed
end Owner1007.Shaft18711
