import Owner1007.WestAfter11CheckPhase0
import Owner1007.WestAfter11CheckPhase1
import Owner1007.WestAfter11CheckPhase2
import Owner1007.WestAfter11CheckPhase3
namespace Owner1007.WestAfter11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked (i : Fin 4) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i = true := by
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases choices with rfl|rfl|rfl|rfl
  · exact node0
  · exact node1
  · exact node2
  · exact node3
theorem region_floor (i : Fin 4) : region i ⊆ soko1_1.board.floor := by
  have all : (List.finRange 4).all (fun i => (region i).all (fun c => decide (c ∈ soko1_1.board.floor))) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked region_floor checked
theorem unique (i : Fin 4) : (locks i).Nodup := by
  have all : (List.finRange 4).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin 4) : (locks i).length = 3 := by
  have all : (List.finRange 4).all (fun i => decide ((locks i).length = 3)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
#print axioms closed
end Owner1007.WestAfter11
