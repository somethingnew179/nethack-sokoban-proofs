/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player80 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 80 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨80,target,direction⟩ : WalkEdge)] else []) = [⟨80,66,.north⟩,⟨80,94,.south⟩,⟨80,67,.northEast⟩,⟨80,95,.southEast⟩,⟨80,93,.southWest⟩] := by decide
theorem walk_player85 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 85 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨85,target,direction⟩ : WalkEdge)] else []) = [⟨85,86,.east⟩,⟨85,99,.south⟩,⟨85,100,.southEast⟩] := by decide
theorem walk_player86 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 86 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨86,target,direction⟩ : WalkEdge)] else []) = [⟨86,87,.east⟩,⟨86,100,.south⟩,⟨86,85,.west⟩,⟨86,99,.southWest⟩] := by decide
theorem walk_player87 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 87 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨87,target,direction⟩ : WalkEdge)] else []) = [⟨87,88,.east⟩,⟨87,86,.west⟩,⟨87,100,.southWest⟩] := by decide
theorem walk_player88 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 88 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨88,target,direction⟩ : WalkEdge)] else []) = [⟨88,89,.east⟩,⟨88,87,.west⟩] := by decide
theorem walk_player89 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 89 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨89,target,direction⟩ : WalkEdge)] else []) = [⟨89,90,.east⟩,⟨89,88,.west⟩] := by decide
theorem walk_player90 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 90 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨90,target,direction⟩ : WalkEdge)] else []) = [⟨90,89,.west⟩] := by decide
theorem walk_player92 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 92 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨92,target,direction⟩ : WalkEdge)] else []) = [⟨92,93,.east⟩,⟨92,106,.south⟩,⟨92,107,.southEast⟩] := by decide
end NetHack.Sokoban41
