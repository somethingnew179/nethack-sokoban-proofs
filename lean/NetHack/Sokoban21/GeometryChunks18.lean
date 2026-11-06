/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player43 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 43 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨43,target,direction⟩ : WalkEdge)] else []) = [⟨43,23,.north⟩,⟨43,44,.east⟩,⟨43,42,.west⟩,⟨43,24,.northEast⟩,⟨43,64,.southEast⟩,⟨43,62,.southWest⟩,⟨43,22,.northWest⟩] := by decide
theorem walk_player44 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 44 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨44,target,direction⟩ : WalkEdge)] else []) = [⟨44,24,.north⟩,⟨44,45,.east⟩,⟨44,64,.south⟩,⟨44,43,.west⟩,⟨44,25,.northEast⟩,⟨44,65,.southEast⟩,⟨44,23,.northWest⟩] := by decide
theorem walk_player45 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 45 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨45,target,direction⟩ : WalkEdge)] else []) = [⟨45,25,.north⟩,⟨45,65,.south⟩,⟨45,44,.west⟩,⟨45,26,.northEast⟩,⟨45,66,.southEast⟩,⟨45,64,.southWest⟩,⟨45,24,.northWest⟩] := by decide
theorem walk_player47 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 47 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨47,target,direction⟩ : WalkEdge)] else []) = [⟨47,27,.north⟩,⟨47,48,.east⟩,⟨47,67,.south⟩,⟨47,28,.northEast⟩,⟨47,68,.southEast⟩,⟨47,66,.southWest⟩,⟨47,26,.northWest⟩] := by decide
theorem walk_player48 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 48 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨48,target,direction⟩ : WalkEdge)] else []) = [⟨48,28,.north⟩,⟨48,68,.south⟩,⟨48,47,.west⟩,⟨48,67,.southWest⟩,⟨48,27,.northWest⟩] := by decide
theorem walk_player50 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 50 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨50,target,direction⟩ : WalkEdge)] else []) = [⟨50,30,.north⟩,⟨50,70,.south⟩,⟨50,31,.northEast⟩,⟨50,71,.southEast⟩] := by decide
theorem walk_player52 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 52 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨52,target,direction⟩ : WalkEdge)] else []) = [⟨52,32,.north⟩,⟨52,72,.south⟩,⟨52,71,.southWest⟩,⟨52,31,.northWest⟩] := by decide
theorem walk_player54 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 54 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨54,target,direction⟩ : WalkEdge)] else []) = [⟨54,34,.north⟩,⟨54,55,.east⟩,⟨54,74,.south⟩,⟨54,35,.northEast⟩,⟨54,75,.southEast⟩] := by decide
end NetHack.Sokoban21
