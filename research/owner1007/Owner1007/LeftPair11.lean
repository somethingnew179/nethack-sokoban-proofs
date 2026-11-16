import Owner1007.LeftPair11CheckFirst
import Owner1007.LeftPair11CheckPhase0
import Owner1007.LeftPair11CheckPhase1
namespace Owner1007.LeftPair11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_floor (i : Fin 1) : cut0Region i ⊆ soko1_1.board.floor := by
  have all : (cut0Region ⟨0,by decide⟩).all (fun c => decide (c ∈ soko1_1.board.floor)) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem first_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes cut0Locks cut0Region cut0Paid := by
  apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked first_floor
  intro i
  have same : i=⟨0,by decide⟩ := Fin.ext (by omega)
  simpa only [same] using first_checked
#print axioms first_closed
theorem checked (i : Fin 2) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i = true := by
  obtain ⟨i,bound⟩ := i
  have choices : i=0 ∨ i=1 := by omega
  rcases choices with rfl|rfl
  · exact node0
  · exact node1
theorem region_floor (i : Fin 2) : region i ⊆ soko1_1.board.floor := by
  have all : (List.finRange 2).all (fun i => (region i).all (fun c => decide (c ∈ soko1_1.board.floor))) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
  FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked region_floor checked
theorem unique (i : Fin 2) : (locks i).Nodup := by
  have all : (List.finRange 2).all (fun i => decide ((locks i).Nodup)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
theorem size (i : Fin 2) : (locks i).length = 2 := by
  have all : (List.finRange 2).all (fun i => decide ((locks i).length = 2)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp all i (by simp))
#print axioms closed
end Owner1007.LeftPair11
