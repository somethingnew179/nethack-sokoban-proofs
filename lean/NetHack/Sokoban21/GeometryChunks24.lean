/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player112 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 112 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨112,target,direction⟩ : WalkEdge)] else []) = [⟨112,92,.north⟩,⟨112,111,.west⟩,⟨112,131,.southWest⟩] := by decide
theorem walk_player114 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 114 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨114,target,direction⟩ : WalkEdge)] else []) = [⟨114,94,.north⟩,⟨114,115,.east⟩,⟨114,134,.south⟩,⟨114,95,.northEast⟩,⟨114,135,.southEast⟩] := by decide
theorem walk_player115 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 115 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨115,target,direction⟩ : WalkEdge)] else []) = [⟨115,95,.north⟩,⟨115,116,.east⟩,⟨115,135,.south⟩,⟨115,114,.west⟩,⟨115,96,.northEast⟩,⟨115,136,.southEast⟩,⟨115,134,.southWest⟩,⟨115,94,.northWest⟩] := by decide
theorem walk_player116 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 116 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨116,target,direction⟩ : WalkEdge)] else []) = [⟨116,96,.north⟩,⟨116,117,.east⟩,⟨116,136,.south⟩,⟨116,115,.west⟩,⟨116,97,.northEast⟩,⟨116,137,.southEast⟩,⟨116,135,.southWest⟩,⟨116,95,.northWest⟩] := by decide
theorem walk_player117 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 117 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨117,target,direction⟩ : WalkEdge)] else []) = [⟨117,97,.north⟩,⟨117,118,.east⟩,⟨117,137,.south⟩,⟨117,116,.west⟩,⟨117,98,.northEast⟩,⟨117,138,.southEast⟩,⟨117,136,.southWest⟩,⟨117,96,.northWest⟩] := by decide
theorem walk_player118 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 118 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨118,target,direction⟩ : WalkEdge)] else []) = [⟨118,98,.north⟩,⟨118,138,.south⟩,⟨118,117,.west⟩,⟨118,137,.southWest⟩,⟨118,97,.northWest⟩] := by decide
theorem walk_player121 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 121 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨121,target,direction⟩ : WalkEdge)] else []) = [⟨121,101,.north⟩,⟨121,122,.east⟩,⟨121,141,.south⟩,⟨121,102,.northEast⟩,⟨121,142,.southEast⟩] := by decide
theorem walk_player122 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 122 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨122,target,direction⟩ : WalkEdge)] else []) = [⟨122,102,.north⟩,⟨122,123,.east⟩,⟨122,142,.south⟩,⟨122,121,.west⟩,⟨122,103,.northEast⟩,⟨122,143,.southEast⟩,⟨122,141,.southWest⟩,⟨122,101,.northWest⟩] := by decide
end NetHack.Sokoban21
