/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks30
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player202 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 202 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨202,target,direction⟩ : WalkEdge)] else []) = [⟨202,182,.north⟩,⟨202,203,.east⟩,⟨202,201,.west⟩,⟨202,183,.northEast⟩,⟨202,181,.northWest⟩] := by decide
theorem walk_player203 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 203 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨203,target,direction⟩ : WalkEdge)] else []) = [⟨203,183,.north⟩,⟨203,202,.west⟩,⟨203,184,.northEast⟩,⟨203,182,.northWest⟩] := by decide
theorem walk_player205 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 205 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨205,target,direction⟩ : WalkEdge)] else []) = [⟨205,185,.north⟩,⟨205,206,.east⟩,⟨205,186,.northEast⟩,⟨205,184,.northWest⟩] := by decide
theorem walk_player206 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 206 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨206,target,direction⟩ : WalkEdge)] else []) = [⟨206,186,.north⟩,⟨206,205,.west⟩,⟨206,187,.northEast⟩,⟨206,185,.northWest⟩] := by decide
theorem reverse_player21 : reverseRow 21 = true := by decide
theorem reverse_player22 : reverseRow 22 = true := by decide
theorem reverse_player23 : reverseRow 23 = true := by decide
theorem reverse_player24 : reverseRow 24 = true := by decide
end NetHack.Sokoban21
