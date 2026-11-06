/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player158 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 158 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨158,target,direction⟩ : WalkEdge)] else []) = [⟨158,138,.north⟩,⟨158,157,.west⟩,⟨158,137,.northWest⟩] := by decide
theorem walk_player162 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 162 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨162,target,direction⟩ : WalkEdge)] else []) = [⟨162,142,.north⟩,⟨162,163,.east⟩,⟨162,182,.south⟩,⟨162,143,.northEast⟩,⟨162,183,.southEast⟩,⟨162,181,.southWest⟩,⟨162,141,.northWest⟩] := by decide
theorem walk_player163 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 163 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨163,target,direction⟩ : WalkEdge)] else []) = [⟨163,143,.north⟩,⟨163,183,.south⟩,⟨163,162,.west⟩,⟨163,184,.southEast⟩,⟨163,182,.southWest⟩,⟨163,142,.northWest⟩] := by decide
theorem walk_player165 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 165 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨165,target,direction⟩ : WalkEdge)] else []) = [⟨165,145,.north⟩,⟨165,166,.east⟩,⟨165,185,.south⟩,⟨165,146,.northEast⟩,⟨165,186,.southEast⟩,⟨165,184,.southWest⟩] := by decide
theorem walk_player166 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 166 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨166,target,direction⟩ : WalkEdge)] else []) = [⟨166,146,.north⟩,⟨166,186,.south⟩,⟨166,165,.west⟩,⟨166,187,.southEast⟩,⟨166,185,.southWest⟩,⟨166,145,.northWest⟩] := by decide
theorem walk_player181 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 181 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨181,target,direction⟩ : WalkEdge)] else []) = [⟨181,182,.east⟩,⟨181,201,.south⟩,⟨181,162,.northEast⟩,⟨181,202,.southEast⟩] := by decide
theorem walk_player182 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 182 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨182,target,direction⟩ : WalkEdge)] else []) = [⟨182,162,.north⟩,⟨182,183,.east⟩,⟨182,202,.south⟩,⟨182,181,.west⟩,⟨182,163,.northEast⟩,⟨182,203,.southEast⟩,⟨182,201,.southWest⟩] := by decide
theorem walk_player183 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 183 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨183,target,direction⟩ : WalkEdge)] else []) = [⟨183,163,.north⟩,⟨183,184,.east⟩,⟨183,203,.south⟩,⟨183,182,.west⟩,⟨183,202,.southWest⟩,⟨183,162,.northWest⟩] := by decide
end NetHack.Sokoban21
