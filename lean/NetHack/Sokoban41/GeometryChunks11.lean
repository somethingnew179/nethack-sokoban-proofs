/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player43 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 43 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨43,target,direction⟩ : WalkEdge)] else []) = [⟨43,29,.north⟩,⟨43,44,.east⟩,⟨43,57,.south⟩,⟨43,30,.northEast⟩,⟨43,58,.southEast⟩] := by decide
theorem walk_player44 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 44 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨44,target,direction⟩ : WalkEdge)] else []) = [⟨44,30,.north⟩,⟨44,45,.east⟩,⟨44,58,.south⟩,⟨44,43,.west⟩,⟨44,31,.northEast⟩,⟨44,57,.southWest⟩,⟨44,29,.northWest⟩] := by decide
theorem walk_player45 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 45 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨45,target,direction⟩ : WalkEdge)] else []) = [⟨45,31,.north⟩,⟨45,46,.east⟩,⟨45,44,.west⟩,⟨45,32,.northEast⟩,⟨45,58,.southWest⟩,⟨45,30,.northWest⟩] := by decide
theorem walk_player46 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 46 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨46,target,direction⟩ : WalkEdge)] else []) = [⟨46,32,.north⟩,⟨46,47,.east⟩,⟨46,45,.west⟩,⟨46,31,.northWest⟩] := by decide
theorem walk_player47 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 47 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨47,target,direction⟩ : WalkEdge)] else []) = [⟨47,48,.east⟩,⟨47,46,.west⟩,⟨47,62,.southEast⟩,⟨47,32,.northWest⟩] := by decide
theorem walk_player48 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 48 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨48,target,direction⟩ : WalkEdge)] else []) = [⟨48,49,.east⟩,⟨48,62,.south⟩,⟨48,47,.west⟩] := by decide
theorem walk_player49 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 49 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨49,target,direction⟩ : WalkEdge)] else []) = [⟨49,50,.east⟩,⟨49,48,.west⟩,⟨49,62,.southWest⟩] := by decide
theorem walk_player50 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 50 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨50,target,direction⟩ : WalkEdge)] else []) = [⟨50,51,.east⟩,⟨50,49,.west⟩,⟨50,37,.northEast⟩] := by decide
end NetHack.Sokoban41
