/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player135 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 135 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨135,target,direction⟩ : WalkEdge)] else []) = [⟨135,115,.north⟩,⟨135,136,.east⟩,⟨135,155,.south⟩,⟨135,134,.west⟩,⟨135,116,.northEast⟩,⟨135,156,.southEast⟩,⟨135,154,.southWest⟩,⟨135,114,.northWest⟩] := by decide
theorem walk_player136 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 136 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨136,target,direction⟩ : WalkEdge)] else []) = [⟨136,116,.north⟩,⟨136,137,.east⟩,⟨136,156,.south⟩,⟨136,135,.west⟩,⟨136,117,.northEast⟩,⟨136,157,.southEast⟩,⟨136,155,.southWest⟩,⟨136,115,.northWest⟩] := by decide
theorem walk_player137 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 137 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨137,target,direction⟩ : WalkEdge)] else []) = [⟨137,117,.north⟩,⟨137,138,.east⟩,⟨137,157,.south⟩,⟨137,136,.west⟩,⟨137,118,.northEast⟩,⟨137,158,.southEast⟩,⟨137,156,.southWest⟩,⟨137,116,.northWest⟩] := by decide
theorem walk_player138 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 138 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨138,target,direction⟩ : WalkEdge)] else []) = [⟨138,118,.north⟩,⟨138,158,.south⟩,⟨138,137,.west⟩,⟨138,157,.southWest⟩,⟨138,117,.northWest⟩] := by decide
theorem walk_player141 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 141 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨141,target,direction⟩ : WalkEdge)] else []) = [⟨141,121,.north⟩,⟨141,142,.east⟩,⟨141,122,.northEast⟩,⟨141,162,.southEast⟩] := by decide
theorem walk_player142 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 142 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨142,target,direction⟩ : WalkEdge)] else []) = [⟨142,122,.north⟩,⟨142,143,.east⟩,⟨142,162,.south⟩,⟨142,141,.west⟩,⟨142,123,.northEast⟩,⟨142,163,.southEast⟩,⟨142,121,.northWest⟩] := by decide
theorem walk_player143 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 143 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨143,target,direction⟩ : WalkEdge)] else []) = [⟨143,123,.north⟩,⟨143,163,.south⟩,⟨143,142,.west⟩,⟨143,162,.southWest⟩,⟨143,122,.northWest⟩] := by decide
theorem walk_player145 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 145 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨145,target,direction⟩ : WalkEdge)] else []) = [⟨145,125,.north⟩,⟨145,146,.east⟩,⟨145,165,.south⟩,⟨145,126,.northEast⟩,⟨145,166,.southEast⟩] := by decide
end NetHack.Sokoban21
