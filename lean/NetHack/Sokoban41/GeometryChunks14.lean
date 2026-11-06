/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player93 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 93 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨93,target,direction⟩ : WalkEdge)] else []) = [⟨93,94,.east⟩,⟨93,107,.south⟩,⟨93,92,.west⟩,⟨93,80,.northEast⟩,⟨93,108,.southEast⟩,⟨93,106,.southWest⟩] := by decide
theorem walk_player94 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 94 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨94,target,direction⟩ : WalkEdge)] else []) = [⟨94,80,.north⟩,⟨94,95,.east⟩,⟨94,108,.south⟩,⟨94,93,.west⟩,⟨94,109,.southEast⟩,⟨94,107,.southWest⟩] := by decide
theorem walk_player95 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 95 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨95,target,direction⟩ : WalkEdge)] else []) = [⟨95,96,.east⟩,⟨95,109,.south⟩,⟨95,94,.west⟩,⟨95,110,.southEast⟩,⟨95,108,.southWest⟩,⟨95,80,.northWest⟩] := by decide
theorem walk_player96 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 96 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨96,target,direction⟩ : WalkEdge)] else []) = [⟨96,110,.south⟩,⟨96,95,.west⟩,⟨96,109,.southWest⟩] := by decide
theorem walk_player99 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 99 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨99,target,direction⟩ : WalkEdge)] else []) = [⟨99,85,.north⟩,⟨99,100,.east⟩,⟨99,86,.northEast⟩,⟨99,114,.southEast⟩] := by decide
theorem walk_player100 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 100 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨100,target,direction⟩ : WalkEdge)] else []) = [⟨100,86,.north⟩,⟨100,114,.south⟩,⟨100,99,.west⟩,⟨100,87,.northEast⟩,⟨100,85,.northWest⟩] := by decide
theorem walk_player106 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 106 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨106,target,direction⟩ : WalkEdge)] else []) = [⟨106,92,.north⟩,⟨106,107,.east⟩,⟨106,120,.south⟩,⟨106,93,.northEast⟩,⟨106,121,.southEast⟩] := by decide
theorem walk_player107 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 107 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨107,target,direction⟩ : WalkEdge)] else []) = [⟨107,93,.north⟩,⟨107,108,.east⟩,⟨107,121,.south⟩,⟨107,106,.west⟩,⟨107,94,.northEast⟩,⟨107,122,.southEast⟩,⟨107,120,.southWest⟩,⟨107,92,.northWest⟩] := by decide
end NetHack.Sokoban41
