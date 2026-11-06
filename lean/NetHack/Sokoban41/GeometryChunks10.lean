/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player25 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 25 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨25,target,direction⟩ : WalkEdge)] else []) = [⟨25,39,.south⟩,⟨25,24,.west⟩,⟨25,38,.southWest⟩] := by decide
theorem walk_player29 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 29 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨29,target,direction⟩ : WalkEdge)] else []) = [⟨29,15,.north⟩,⟨29,30,.east⟩,⟨29,43,.south⟩,⟨29,16,.northEast⟩,⟨29,44,.southEast⟩] := by decide
theorem walk_player30 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 30 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨30,target,direction⟩ : WalkEdge)] else []) = [⟨30,16,.north⟩,⟨30,31,.east⟩,⟨30,44,.south⟩,⟨30,29,.west⟩,⟨30,17,.northEast⟩,⟨30,45,.southEast⟩,⟨30,43,.southWest⟩,⟨30,15,.northWest⟩] := by decide
theorem walk_player31 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 31 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨31,target,direction⟩ : WalkEdge)] else []) = [⟨31,17,.north⟩,⟨31,32,.east⟩,⟨31,45,.south⟩,⟨31,30,.west⟩,⟨31,18,.northEast⟩,⟨31,46,.southEast⟩,⟨31,44,.southWest⟩,⟨31,16,.northWest⟩] := by decide
theorem walk_player32 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 32 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨32,target,direction⟩ : WalkEdge)] else []) = [⟨32,18,.north⟩,⟨32,46,.south⟩,⟨32,31,.west⟩,⟨32,47,.southEast⟩,⟨32,45,.southWest⟩,⟨32,17,.northWest⟩] := by decide
theorem walk_player37 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 37 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨37,target,direction⟩ : WalkEdge)] else []) = [⟨37,23,.north⟩,⟨37,38,.east⟩,⟨37,51,.south⟩,⟨37,24,.northEast⟩,⟨37,52,.southEast⟩,⟨37,50,.southWest⟩] := by decide
theorem walk_player38 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 38 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨38,target,direction⟩ : WalkEdge)] else []) = [⟨38,24,.north⟩,⟨38,39,.east⟩,⟨38,52,.south⟩,⟨38,37,.west⟩,⟨38,25,.northEast⟩,⟨38,53,.southEast⟩,⟨38,51,.southWest⟩,⟨38,23,.northWest⟩] := by decide
theorem walk_player39 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 39 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨39,target,direction⟩ : WalkEdge)] else []) = [⟨39,25,.north⟩,⟨39,53,.south⟩,⟨39,38,.west⟩,⟨39,52,.southWest⟩,⟨39,24,.northWest⟩] := by decide
end NetHack.Sokoban41
