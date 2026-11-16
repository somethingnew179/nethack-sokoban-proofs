import Owner1007.Parked18811CheckPhase0
import Owner1007.Parked18811CheckPhase1
import Owner1007.Parked18811CheckPhase2
import Owner1007.Parked18811CheckPhase3
import Owner1007.Parked18811CheckPhase4
import Owner1007.Parked18811CheckPhase5
import Owner1007.Parked18811CheckPhase6
import Owner1007.Parked18811CheckPhase7
import Owner1007.Parked18811CheckPhase8
namespace Owner1007.Parked18811
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked (i : Fin 9) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i = true := by
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
  · exact node4
  · exact node5
  · exact node6
  · exact node7
  · exact node8
theorem region_floor (i : Fin 9) : region i ⊆ soko1_1.board.floor := by
  have all : (List.finRange 9).all (fun i => (region i).all (fun c => decide (c ∈ soko1_1.board.floor))) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked region_floor checked
theorem unique (i : Fin 9) : (locks i).Nodup := by
  have all : (List.finRange 9).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin 9) : (locks i).length = 4 := by
  have all : (List.finRange 9).all (fun i => decide ((locks i).length = 4)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
#print axioms closed
end Owner1007.Parked18811
