/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player146 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 146 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨146,target,direction⟩ : WalkEdge)] else []) = [⟨146,126,.north⟩,⟨146,166,.south⟩,⟨146,145,.west⟩,⟨146,127,.northEast⟩,⟨146,165,.southWest⟩,⟨146,125,.northWest⟩] := by decide
theorem walk_player148 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 148 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨148,target,direction⟩ : WalkEdge)] else []) = [⟨148,149,.east⟩,⟨148,129,.northEast⟩,⟨148,127,.northWest⟩] := by decide
theorem walk_player149 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 149 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨149,target,direction⟩ : WalkEdge)] else []) = [⟨149,129,.north⟩,⟨149,150,.east⟩,⟨149,148,.west⟩,⟨149,130,.northEast⟩] := by decide
theorem walk_player150 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 150 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨150,target,direction⟩ : WalkEdge)] else []) = [⟨150,130,.north⟩,⟨150,149,.west⟩,⟨150,131,.northEast⟩,⟨150,129,.northWest⟩] := by decide
theorem walk_player154 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 154 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨154,target,direction⟩ : WalkEdge)] else []) = [⟨154,134,.north⟩,⟨154,155,.east⟩,⟨154,135,.northEast⟩] := by decide
theorem walk_player155 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 155 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨155,target,direction⟩ : WalkEdge)] else []) = [⟨155,135,.north⟩,⟨155,156,.east⟩,⟨155,154,.west⟩,⟨155,136,.northEast⟩,⟨155,134,.northWest⟩] := by decide
theorem walk_player156 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 156 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨156,target,direction⟩ : WalkEdge)] else []) = [⟨156,136,.north⟩,⟨156,157,.east⟩,⟨156,155,.west⟩,⟨156,137,.northEast⟩,⟨156,135,.northWest⟩] := by decide
theorem walk_player157 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 157 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨157,target,direction⟩ : WalkEdge)] else []) = [⟨157,137,.north⟩,⟨157,158,.east⟩,⟨157,156,.west⟩,⟨157,138,.northEast⟩,⟨157,136,.northWest⟩] := by decide
end NetHack.Sokoban21
