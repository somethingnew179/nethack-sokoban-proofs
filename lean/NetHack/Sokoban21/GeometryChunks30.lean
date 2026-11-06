/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks29
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player192 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 192 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨192,target,direction⟩ : WalkEdge)] else []) = [⟨192,193,.east⟩,⟨192,191,.west⟩] := by decide
theorem walk_player193 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 193 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨193,target,direction⟩ : WalkEdge)] else []) = [⟨193,194,.east⟩,⟨193,192,.west⟩] := by decide
theorem walk_player194 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 194 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨194,target,direction⟩ : WalkEdge)] else []) = [⟨194,195,.east⟩,⟨194,193,.west⟩] := by decide
theorem walk_player195 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 195 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨195,target,direction⟩ : WalkEdge)] else []) = [⟨195,196,.east⟩,⟨195,194,.west⟩] := by decide
theorem walk_player196 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 196 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨196,target,direction⟩ : WalkEdge)] else []) = [⟨196,197,.east⟩,⟨196,195,.west⟩] := by decide
theorem walk_player197 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 197 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨197,target,direction⟩ : WalkEdge)] else []) = [⟨197,198,.east⟩,⟨197,196,.west⟩] := by decide
theorem walk_player198 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 198 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨198,target,direction⟩ : WalkEdge)] else []) = [⟨198,197,.west⟩] := by decide
theorem walk_player201 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 201 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨201,target,direction⟩ : WalkEdge)] else []) = [⟨201,181,.north⟩,⟨201,202,.east⟩,⟨201,182,.northEast⟩] := by decide
end NetHack.Sokoban21
