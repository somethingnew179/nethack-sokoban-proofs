import Owner1007.PostCuts11CheckRight
import Owner1007.PostCuts11CheckEntry
namespace Owner1007.PostCuts11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem right_floor (i : Fin 1) : rightRegion i ⊆ soko1_1.board.floor := by
  have all : (rightRegion ⟨0,by decide⟩).all (fun c => decide (c ∈ soko1_1.board.floor)) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem right_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes rightLocks rightRegion rightPaid := by
  apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked right_floor
  intro i
  have same : i=⟨0,by decide⟩ := Fin.ext (by omega)
  simpa only [same] using right_checked
#print axioms right_closed
theorem entry_floor (i : Fin 1) : entryRegion i ⊆ soko1_1.board.floor := by
  have all : (entryRegion ⟨0,by decide⟩).all (fun c => decide (c ∈ soko1_1.board.floor)) = true := by decide +kernel
  intro c found
  exact of_decide_eq_true (List.all_eq_true.mp all c found)
theorem entry_closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes entryLocks entryRegion entryPaid := by
  apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked entry_floor
  intro i
  have same : i=⟨0,by decide⟩ := Fin.ext (by omega)
  simpa only [same] using entry_checked
#print axioms entry_closed
end Owner1007.PostCuts11
