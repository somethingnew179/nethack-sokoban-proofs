/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player102 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 102 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨102,target,direction⟩ : WalkEdge)] else []) = [⟨102,82,.north⟩,⟨102,103,.east⟩,⟨102,122,.south⟩,⟨102,101,.west⟩,⟨102,123,.southEast⟩,⟨102,121,.southWest⟩] := by decide
theorem walk_player103 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 103 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨103,target,direction⟩ : WalkEdge)] else []) = [⟨103,123,.south⟩,⟨103,102,.west⟩,⟨103,84,.northEast⟩,⟨103,122,.southWest⟩,⟨103,82,.northWest⟩] := by decide
theorem walk_player106 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 106 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨106,target,direction⟩ : WalkEdge)] else []) = [⟨106,107,.east⟩,⟨106,126,.south⟩,⟨106,87,.northEast⟩,⟨106,127,.southEast⟩,⟨106,125,.southWest⟩,⟨106,85,.northWest⟩] := by decide
theorem walk_player107 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 107 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨107,target,direction⟩ : WalkEdge)] else []) = [⟨107,87,.north⟩,⟨107,108,.east⟩,⟨107,127,.south⟩,⟨107,106,.west⟩,⟨107,88,.northEast⟩,⟨107,126,.southWest⟩] := by decide
theorem walk_player108 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 108 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨108,target,direction⟩ : WalkEdge)] else []) = [⟨108,88,.north⟩,⟨108,109,.east⟩,⟨108,107,.west⟩,⟨108,129,.southEast⟩,⟨108,127,.southWest⟩,⟨108,87,.northWest⟩] := by decide
theorem walk_player109 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 109 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨109,target,direction⟩ : WalkEdge)] else []) = [⟨109,110,.east⟩,⟨109,129,.south⟩,⟨109,108,.west⟩,⟨109,90,.northEast⟩,⟨109,130,.southEast⟩,⟨109,88,.northWest⟩] := by decide
theorem walk_player110 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 110 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨110,target,direction⟩ : WalkEdge)] else []) = [⟨110,90,.north⟩,⟨110,111,.east⟩,⟨110,130,.south⟩,⟨110,109,.west⟩,⟨110,131,.southEast⟩,⟨110,129,.southWest⟩] := by decide
theorem walk_player111 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 111 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨111,target,direction⟩ : WalkEdge)] else []) = [⟨111,112,.east⟩,⟨111,131,.south⟩,⟨111,110,.west⟩,⟨111,92,.northEast⟩,⟨111,130,.southWest⟩,⟨111,90,.northWest⟩] := by decide
end NetHack.Sokoban21
