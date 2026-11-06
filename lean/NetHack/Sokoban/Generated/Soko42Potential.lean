/- Finite source-board potential certificate. Proposed by external matching;
all inequalities and the numerical bound are checked by the Lean kernel.
This is a lower bound, NOT an assertion that a solution attaining it exists. -/
import NetHack.Sokoban.Maps
import NetHack.Sokoban.Certificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

open Certificates LowerBounds

def soko4_2Debt : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 1, 2, 3, 4, 3, 2, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 5, 4, 3, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 7, 6, 5, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 9, 8, 7, 6, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 11, 10, 9, 8, 7, 0, 0, 0, 14, 14, 14, 14, 14, 13, 13, 12, 11, 10, 9, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def soko4_2Credit : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14, 14, 14, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def soko4_2Potential : Potential := tablePotential soko4_2Debt soko4_2Credit

theorem soko4_2_absorption_checked : dominates soko4_2Credit soko4_2Debt = true := by decide

theorem soko4_2_edges_checked : edgesCheck soko4_2.board soko4_2Potential = true := by decide

theorem soko4_2_potential_valid : Valid soko4_2.board soko4_2Potential :=
  valid_of_tables soko4_2.board soko4_2Debt soko4_2Credit
    soko4_2_absorption_checked soko4_2_edges_checked

theorem soko4_2_initial_potential : soko4_2Potential.value soko4_2.initial = 80 := by decide

/-- Every successful finite trace in the explicit rolling/no-collision puzzle
profile needs at least 80 initiated pushes. This theorem does not cover
tools, new boulders, teleportation, monsters, rolling collisions or door actions. -/
theorem soko4_2_pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board soko4_2.initial directions final pushes moves)
    (completed : Goal final) : 80 ≤ pushes := by
  apply pushes_minimal_of_potential soko4_2_potential_valid.stepBound
    soko4_2_potential_valid.goalBound 80 soko4_2_initial_potential trace completed

end NetHack.Sokoban.Generated
