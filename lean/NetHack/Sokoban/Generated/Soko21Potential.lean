/- Finite source-board potential certificate. Proposed by external matching;
all inequalities and the numerical bound are checked by the Lean kernel.
This is a lower bound, NOT an assertion that a solution attaining it exists. -/
import NetHack.Sokoban.Maps
import NetHack.Sokoban.Certificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace NetHack.Sokoban.Generated

open Certificates LowerBounds

def soko2_1Debt : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 6, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 12, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 13, 0, 15, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 14, 0, 16, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 17, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def soko2_1Credit : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def soko2_1Potential : Potential := tablePotential soko2_1Debt soko2_1Credit

theorem soko2_1_absorption_checked : dominates soko2_1Credit soko2_1Debt = true := by decide

theorem soko2_1_edges_checked : edgesCheck soko2_1.board soko2_1Potential = true := by decide

theorem soko2_1_potential_valid : Valid soko2_1.board soko2_1Potential :=
  valid_of_tables soko2_1.board soko2_1Debt soko2_1Credit
    soko2_1_absorption_checked soko2_1_edges_checked

theorem soko2_1_initial_potential : soko2_1Potential.value soko2_1.initial = 103 := by decide

/-- Every successful finite trace in the explicit rolling/no-collision puzzle
profile needs at least 103 initiated pushes. This theorem does not cover
tools, new boulders, teleportation, monsters, rolling collisions or door actions. -/
theorem soko2_1_pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko2_1.board soko2_1.initial directions final pushes moves)
    (completed : Goal final) : 103 ≤ pushes := by
  apply pushes_minimal_of_potential soko2_1_potential_valid.stepBound
    soko2_1_potential_valid.goalBound 103 soko2_1_initial_potential trace completed

end NetHack.Sokoban.Generated
