/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player66 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 66 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨66,target,direction⟩ : WalkEdge)] else []) = [⟨66,67,.east⟩,⟨66,65,.west⟩,⟨66,47,.northEast⟩,⟨66,87,.southEast⟩,⟨66,85,.southWest⟩,⟨66,45,.northWest⟩] := by decide
theorem walk_player67 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 67 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨67,target,direction⟩ : WalkEdge)] else []) = [⟨67,47,.north⟩,⟨67,68,.east⟩,⟨67,87,.south⟩,⟨67,66,.west⟩,⟨67,48,.northEast⟩,⟨67,88,.southEast⟩] := by decide
theorem walk_player68 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 68 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨68,target,direction⟩ : WalkEdge)] else []) = [⟨68,48,.north⟩,⟨68,88,.south⟩,⟨68,67,.west⟩,⟨68,87,.southWest⟩,⟨68,47,.northWest⟩] := by decide
theorem walk_player70 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 70 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨70,target,direction⟩ : WalkEdge)] else []) = [⟨70,50,.north⟩,⟨70,71,.east⟩,⟨70,90,.south⟩] := by decide
theorem walk_player71 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 71 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨71,target,direction⟩ : WalkEdge)] else []) = [⟨71,72,.east⟩,⟨71,70,.west⟩,⟨71,52,.northEast⟩,⟨71,92,.southEast⟩,⟨71,90,.southWest⟩,⟨71,50,.northWest⟩] := by decide
theorem walk_player72 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 72 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨72,target,direction⟩ : WalkEdge)] else []) = [⟨72,52,.north⟩,⟨72,92,.south⟩,⟨72,71,.west⟩] := by decide
theorem walk_player74 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 74 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨74,target,direction⟩ : WalkEdge)] else []) = [⟨74,54,.north⟩,⟨74,75,.east⟩,⟨74,94,.south⟩,⟨74,55,.northEast⟩,⟨74,95,.southEast⟩] := by decide
theorem walk_player75 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 75 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨75,target,direction⟩ : WalkEdge)] else []) = [⟨75,55,.north⟩,⟨75,76,.east⟩,⟨75,95,.south⟩,⟨75,74,.west⟩,⟨75,56,.northEast⟩,⟨75,96,.southEast⟩,⟨75,94,.southWest⟩,⟨75,54,.northWest⟩] := by decide
end NetHack.Sokoban21
