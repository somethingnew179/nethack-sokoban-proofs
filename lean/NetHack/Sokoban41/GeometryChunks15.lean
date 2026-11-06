/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player108 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 108 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨108,target,direction⟩ : WalkEdge)] else []) = [⟨108,94,.north⟩,⟨108,109,.east⟩,⟨108,122,.south⟩,⟨108,107,.west⟩,⟨108,95,.northEast⟩,⟨108,123,.southEast⟩,⟨108,121,.southWest⟩,⟨108,93,.northWest⟩] := by decide
theorem walk_player109 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 109 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨109,target,direction⟩ : WalkEdge)] else []) = [⟨109,95,.north⟩,⟨109,110,.east⟩,⟨109,123,.south⟩,⟨109,108,.west⟩,⟨109,96,.northEast⟩,⟨109,124,.southEast⟩,⟨109,122,.southWest⟩,⟨109,94,.northWest⟩] := by decide
theorem walk_player110 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 110 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨110,target,direction⟩ : WalkEdge)] else []) = [⟨110,96,.north⟩,⟨110,124,.south⟩,⟨110,109,.west⟩,⟨110,123,.southWest⟩,⟨110,95,.northWest⟩] := by decide
theorem walk_player114 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 114 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨114,target,direction⟩ : WalkEdge)] else []) = [⟨114,100,.north⟩,⟨114,128,.south⟩,⟨114,99,.northWest⟩] := by decide
theorem walk_player120 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 120 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨120,target,direction⟩ : WalkEdge)] else []) = [⟨120,106,.north⟩,⟨120,121,.east⟩,⟨120,134,.south⟩,⟨120,107,.northEast⟩,⟨120,135,.southEast⟩] := by decide
theorem walk_player121 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 121 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨121,target,direction⟩ : WalkEdge)] else []) = [⟨121,107,.north⟩,⟨121,122,.east⟩,⟨121,135,.south⟩,⟨121,120,.west⟩,⟨121,108,.northEast⟩,⟨121,136,.southEast⟩,⟨121,134,.southWest⟩,⟨121,106,.northWest⟩] := by decide
theorem walk_player122 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 122 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨122,target,direction⟩ : WalkEdge)] else []) = [⟨122,108,.north⟩,⟨122,123,.east⟩,⟨122,136,.south⟩,⟨122,121,.west⟩,⟨122,109,.northEast⟩,⟨122,137,.southEast⟩,⟨122,135,.southWest⟩,⟨122,107,.northWest⟩] := by decide
theorem walk_player123 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 123 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨123,target,direction⟩ : WalkEdge)] else []) = [⟨123,109,.north⟩,⟨123,124,.east⟩,⟨123,137,.south⟩,⟨123,122,.west⟩,⟨123,110,.northEast⟩,⟨123,138,.southEast⟩,⟨123,136,.southWest⟩,⟨123,108,.northWest⟩] := by decide
end NetHack.Sokoban41
