/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player143 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 143 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨143,target,direction⟩ : WalkEdge)] else []) = [⟨143,144,.east⟩,⟨143,157,.south⟩,⟨143,142,.west⟩,⟨143,156,.southWest⟩,⟨143,128,.northWest⟩] := by decide
theorem walk_player144 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 144 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨144,target,direction⟩ : WalkEdge)] else []) = [⟨144,145,.east⟩,⟨144,143,.west⟩,⟨144,157,.southWest⟩] := by decide
theorem walk_player145 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 145 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨145,target,direction⟩ : WalkEdge)] else []) = [⟨145,146,.east⟩,⟨145,144,.west⟩] := by decide
theorem walk_player146 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 146 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨146,target,direction⟩ : WalkEdge)] else []) = [⟨146,147,.east⟩,⟨146,145,.west⟩] := by decide
theorem walk_player147 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 147 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨147,target,direction⟩ : WalkEdge)] else []) = [⟨147,148,.east⟩,⟨147,146,.west⟩,⟨147,134,.northEast⟩] := by decide
theorem walk_player148 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 148 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨148,target,direction⟩ : WalkEdge)] else []) = [⟨148,134,.north⟩,⟨148,149,.east⟩,⟨148,147,.west⟩,⟨148,135,.northEast⟩] := by decide
theorem walk_player149 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 149 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨149,target,direction⟩ : WalkEdge)] else []) = [⟨149,135,.north⟩,⟨149,150,.east⟩,⟨149,148,.west⟩,⟨149,136,.northEast⟩,⟨149,134,.northWest⟩] := by decide
theorem walk_player150 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 150 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨150,target,direction⟩ : WalkEdge)] else []) = [⟨150,136,.north⟩,⟨150,151,.east⟩,⟨150,149,.west⟩,⟨150,137,.northEast⟩,⟨150,135,.northWest⟩] := by decide
end NetHack.Sokoban41
