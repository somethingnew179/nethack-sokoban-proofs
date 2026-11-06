/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player123 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 123 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨123,target,direction⟩ : WalkEdge)] else []) = [⟨123,103,.north⟩,⟨123,143,.south⟩,⟨123,122,.west⟩,⟨123,142,.southWest⟩,⟨123,102,.northWest⟩] := by decide
theorem walk_player125 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 125 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨125,target,direction⟩ : WalkEdge)] else []) = [⟨125,126,.east⟩,⟨125,145,.south⟩,⟨125,106,.northEast⟩,⟨125,146,.southEast⟩] := by decide
theorem walk_player126 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 126 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨126,target,direction⟩ : WalkEdge)] else []) = [⟨126,106,.north⟩,⟨126,127,.east⟩,⟨126,146,.south⟩,⟨126,125,.west⟩,⟨126,107,.northEast⟩,⟨126,145,.southWest⟩] := by decide
theorem walk_player127 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 127 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨127,target,direction⟩ : WalkEdge)] else []) = [⟨127,107,.north⟩,⟨127,126,.west⟩,⟨127,108,.northEast⟩,⟨127,148,.southEast⟩,⟨127,146,.southWest⟩,⟨127,106,.northWest⟩] := by decide
theorem walk_player129 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 129 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨129,target,direction⟩ : WalkEdge)] else []) = [⟨129,109,.north⟩,⟨129,130,.east⟩,⟨129,149,.south⟩,⟨129,110,.northEast⟩,⟨129,150,.southEast⟩,⟨129,148,.southWest⟩,⟨129,108,.northWest⟩] := by decide
theorem walk_player130 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 130 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨130,target,direction⟩ : WalkEdge)] else []) = [⟨130,110,.north⟩,⟨130,131,.east⟩,⟨130,150,.south⟩,⟨130,129,.west⟩,⟨130,111,.northEast⟩,⟨130,149,.southWest⟩,⟨130,109,.northWest⟩] := by decide
theorem walk_player131 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 131 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨131,target,direction⟩ : WalkEdge)] else []) = [⟨131,111,.north⟩,⟨131,130,.west⟩,⟨131,112,.northEast⟩,⟨131,150,.southWest⟩,⟨131,110,.northWest⟩] := by decide
theorem walk_player134 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 134 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨134,target,direction⟩ : WalkEdge)] else []) = [⟨134,114,.north⟩,⟨134,135,.east⟩,⟨134,154,.south⟩,⟨134,115,.northEast⟩,⟨134,155,.southEast⟩] := by decide
end NetHack.Sokoban21
