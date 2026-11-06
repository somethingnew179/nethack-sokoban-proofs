/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player76 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 76 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨76,target,direction⟩ : WalkEdge)] else []) = [⟨76,56,.north⟩,⟨76,77,.east⟩,⟨76,96,.south⟩,⟨76,75,.west⟩,⟨76,57,.northEast⟩,⟨76,97,.southEast⟩,⟨76,95,.southWest⟩,⟨76,55,.northWest⟩] := by decide
theorem walk_player77 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 77 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨77,target,direction⟩ : WalkEdge)] else []) = [⟨77,57,.north⟩,⟨77,78,.east⟩,⟨77,97,.south⟩,⟨77,76,.west⟩,⟨77,58,.northEast⟩,⟨77,98,.southEast⟩,⟨77,96,.southWest⟩,⟨77,56,.northWest⟩] := by decide
theorem walk_player78 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 78 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨78,target,direction⟩ : WalkEdge)] else []) = [⟨78,58,.north⟩,⟨78,98,.south⟩,⟨78,77,.west⟩,⟨78,97,.southWest⟩,⟨78,57,.northWest⟩] := by decide
theorem walk_player82 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 82 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨82,target,direction⟩ : WalkEdge)] else []) = [⟨82,62,.north⟩,⟨82,102,.south⟩,⟨82,103,.southEast⟩,⟨82,101,.southWest⟩,⟨82,61,.northWest⟩] := by decide
theorem walk_player84 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 84 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨84,target,direction⟩ : WalkEdge)] else []) = [⟨84,64,.north⟩,⟨84,85,.east⟩,⟨84,65,.northEast⟩,⟨84,103,.southWest⟩] := by decide
theorem walk_player85 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 85 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨85,target,direction⟩ : WalkEdge)] else []) = [⟨85,65,.north⟩,⟨85,84,.west⟩,⟨85,66,.northEast⟩,⟨85,106,.southEast⟩,⟨85,64,.northWest⟩] := by decide
theorem walk_player87 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 87 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨87,target,direction⟩ : WalkEdge)] else []) = [⟨87,67,.north⟩,⟨87,88,.east⟩,⟨87,107,.south⟩,⟨87,68,.northEast⟩,⟨87,108,.southEast⟩,⟨87,106,.southWest⟩,⟨87,66,.northWest⟩] := by decide
theorem walk_player88 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 88 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨88,target,direction⟩ : WalkEdge)] else []) = [⟨88,68,.north⟩,⟨88,108,.south⟩,⟨88,87,.west⟩,⟨88,109,.southEast⟩,⟨88,107,.southWest⟩,⟨88,67,.northWest⟩] := by decide
end NetHack.Sokoban21
