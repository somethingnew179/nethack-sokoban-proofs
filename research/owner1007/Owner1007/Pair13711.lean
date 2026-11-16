import Owner1007.Pair13711Check00
import Owner1007.Pair13711Check01
import Owner1007.Pair13711Check02
import Owner1007.Pair13711Check03
import Owner1007.Pair13711Check04
import Owner1007.Pair13711Check05
import Owner1007.Pair13711Check06
import Owner1007.Pair13711Check07
import Owner1007.Pair13711Check08
import Owner1007.Pair13711Check09
namespace Owner1007.Pair13711
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked (i : Fin 10) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node0_north
     · exact node0_south
     · exact node0_east
     · exact node0_west
     · exact node0_northEast
     · exact node0_northWest
     · exact node0_southEast
     · exact node0_southWest
   · exact node0_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node1_north
     · exact node1_south
     · exact node1_east
     · exact node1_west
     · exact node1_northEast
     · exact node1_northWest
     · exact node1_southEast
     · exact node1_southWest
   · exact node1_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node2_north
     · exact node2_south
     · exact node2_east
     · exact node2_west
     · exact node2_northEast
     · exact node2_northWest
     · exact node2_southEast
     · exact node2_southWest
   · exact node2_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node3_north
     · exact node3_south
     · exact node3_east
     · exact node3_west
     · exact node3_northEast
     · exact node3_northWest
     · exact node3_southEast
     · exact node3_southWest
   · exact node3_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node4_north
     · exact node4_south
     · exact node4_east
     · exact node4_west
     · exact node4_northEast
     · exact node4_northWest
     · exact node4_southEast
     · exact node4_southWest
   · exact node4_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node5_north
     · exact node5_south
     · exact node5_east
     · exact node5_west
     · exact node5_northEast
     · exact node5_northWest
     · exact node5_southEast
     · exact node5_southWest
   · exact node5_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node6_north
     · exact node6_south
     · exact node6_east
     · exact node6_west
     · exact node6_northEast
     · exact node6_northWest
     · exact node6_southEast
     · exact node6_southWest
   · exact node6_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node7_north
     · exact node7_south
     · exact node7_east
     · exact node7_west
     · exact node7_northEast
     · exact node7_northWest
     · exact node7_southEast
     · exact node7_southWest
   · exact node7_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node8_north
     · exact node8_south
     · exact node8_east
     · exact node8_west
     · exact node8_northEast
     · exact node8_northWest
     · exact node8_southEast
     · exact node8_southWest
   · exact node8_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node9_north
     · exact node9_south
     · exact node9_east
     · exact node9_west
     · exact node9_northEast
     · exact node9_northWest
     · exact node9_southEast
     · exact node9_southWest
   · exact node9_push

theorem floors (i : Fin 10) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 10).all (fun i => (region i).all (fun c => decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked
#print axioms closed

end Owner1007.Pair13711
