/- Finite source-board potential certificate. Proposed by external matching;
all inequalities and the numerical bound are checked by the Lean kernel.
This is a lower bound, NOT an assertion that a solution attaining it exists. -/
import NetHack.Sokoban.Maps
import NetHack.Sokoban.Certificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

open Certificates LowerBounds

def soko4_1Debt : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 19, 20, 21, 20, 0, 0, 0, 10, 11, 10, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 14, 13, 12, 11, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 15, 14, 13, 12, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 16, 15, 14, 13, 0, 0, 0, 0, 18, 18, 18, 18, 18, 17, 17, 16, 15, 14, 0, 0, 0, 0, 0, 0]
def soko4_1Credit : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 18, 18, 18, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def soko4_1Potential : Potential := tablePotential soko4_1Debt soko4_1Credit

theorem soko4_1_absorption_checked : dominates soko4_1Credit soko4_1Debt = true := by decide

theorem soko4_1_edges_checked : edgesCheck soko4_1.board soko4_1Potential = true := by decide

theorem soko4_1_potential_valid : Valid soko4_1.board soko4_1Potential :=
  valid_of_tables soko4_1.board soko4_1Debt soko4_1Credit
    soko4_1_absorption_checked soko4_1_edges_checked

theorem soko4_1_initial_potential : soko4_1Potential.value soko4_1.initial = 70 := by decide

/-- Every successful finite trace in the explicit rolling/no-collision puzzle
profile needs at least 70 initiated pushes. This theorem does not cover
tools, new boulders, teleportation, monsters, rolling collisions or door actions. -/
theorem soko4_1_pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_1.board soko4_1.initial directions final pushes moves)
    (completed : Goal final) : 70 ≤ pushes := by
  apply pushes_minimal_of_potential soko4_1_potential_valid.stepBound
    soko4_1_potential_valid.goalBound 70 soko4_1_initial_potential trace completed

end NetHack.Sokoban.Generated
