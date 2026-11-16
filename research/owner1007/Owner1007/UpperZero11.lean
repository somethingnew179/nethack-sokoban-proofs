import Owner1007.UpperZero11CheckPhase0
import Owner1007.UpperZero11CheckPhase1
import Owner1007.UpperZero11CheckPhase2
import Owner1007.UpperZero11CheckPhase3
import Owner1007.UpperZero11CheckPhase4
import Owner1007.UpperZero11CheckPhase5
import Owner1007.UpperZero11CheckPhase6
import Owner1007.UpperZero11CheckPhase7
import Owner1007.UpperZero11CheckPhase8
import Owner1007.UpperZero11CheckPhase9
import Owner1007.UpperZero11CheckPhase10
import Owner1007.UpperZero11CheckPhase11
import Owner1007.UpperZero11CheckPhase12
import Owner1007.UpperZero11CheckPhase13
import Owner1007.UpperZero11CheckPhase14
import Owner1007.UpperZero11CheckPhase15
import Owner1007.UpperZero11CheckPhase16
import Owner1007.UpperZero11CheckPhase17
import Owner1007.UpperZero11CheckPhase18
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked (i : Fin 19) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i = true := by
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 := by omega
  rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
  · exact node4
  · exact node5
  · exact node6
  · exact node7
  · exact node8
  · exact node9
  · exact node10
  · exact node11
  · exact node12
  · exact node13
  · exact node14
  · exact node15
  · exact node16
  · exact node17
  · exact node18
theorem region_floor (i : Fin 19) : region i ⊆ soko1_1.board.floor := by
  have all : (List.finRange 19).all (fun i => (region i).all (fun c => decide (c ∈ soko1_1.board.floor))) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked region_floor checked
theorem unique (i : Fin 19) : (locks i).Nodup := by
  have all : (List.finRange 19).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin 19) : (locks i).length = 3 := by
  have all : (List.finRange 19).all (fun i => decide ((locks i).length = 3)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
#print axioms closed
end Owner1007.UpperZero11
