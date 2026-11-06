import NetHack.Soko12Forward220.Unified.P00.PhysicalAll
import NetHack.Soko12Forward220.Unified.P01.PhysicalAll
import NetHack.Soko12Forward220.Unified.P02.PhysicalAll
import NetHack.Soko12Forward220.Unified.P03.PhysicalAll
import NetHack.Soko12Forward220.Unified.P04.PhysicalAll
import NetHack.Soko12Forward220.Unified.P05.PhysicalAll
import NetHack.Soko12Forward220.Unified.CheckedSystem
import NetHack.Soko12Forward220.Reduction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Verified220
open NetHack.Sokoban
theorem all_local_early : NetHack.Soko12Forward220.Reduction.LocalEarly := by
  intro phase active hero member direction
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
  · exact local_of_covered checkedSystem checkedSystem_data 0 (by decide +kernel) hero direction
      (P00.all_physical hero member direction)
  · exact local_of_covered checkedSystem checkedSystem_data 1 (by decide +kernel) hero direction
      (P01.all_physical hero member direction)
  · exact local_of_covered checkedSystem checkedSystem_data 2 (by decide +kernel) hero direction
      (P02.all_physical hero member direction)
  · exact local_of_covered checkedSystem checkedSystem_data 3 (by decide +kernel) hero direction
      (P03.all_physical hero member direction)
  · exact local_of_covered checkedSystem checkedSystem_data 4 (by decide +kernel) hero direction
      (P04.all_physical hero member direction)
  · exact local_of_covered checkedSystem checkedSystem_data 5 (by decide +kernel) hero direction
      (P05.all_physical hero member direction)
/-- Every completing original1-2 Trace in the unchanged puzzle profile.
All18 phases and all actions are retained. This lower220 is not minimum235. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves)
    (completed : Goal final) : 220 ≤ pushes :=
  NetHack.Soko12Forward220.Reduction.lower_bound_if_early all_local_early trace completed
theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko1_2.board soko1_2.initial directions final pushes moves)
    (completed : Goal final) : 220 ≤ moves :=
  Nat.le_trans (pushes_lower_bound trace completed) (LowerBounds.trace_pushes_le_moves trace)
end NetHack.Soko12Forward220.Unified.Verified220
