/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks28
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player184 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 184 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨184,target,direction⟩ : WalkEdge)] else []) = [⟨184,185,.east⟩,⟨184,183,.west⟩,⟨184,165,.northEast⟩,⟨184,205,.southEast⟩,⟨184,203,.southWest⟩,⟨184,163,.northWest⟩] := by decide
theorem walk_player185 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 185 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨185,target,direction⟩ : WalkEdge)] else []) = [⟨185,165,.north⟩,⟨185,186,.east⟩,⟨185,205,.south⟩,⟨185,184,.west⟩,⟨185,166,.northEast⟩,⟨185,206,.southEast⟩] := by decide
theorem walk_player186 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 186 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨186,target,direction⟩ : WalkEdge)] else []) = [⟨186,166,.north⟩,⟨186,187,.east⟩,⟨186,206,.south⟩,⟨186,185,.west⟩,⟨186,205,.southWest⟩,⟨186,165,.northWest⟩] := by decide
theorem walk_player187 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 187 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨187,target,direction⟩ : WalkEdge)] else []) = [⟨187,188,.east⟩,⟨187,186,.west⟩,⟨187,206,.southWest⟩,⟨187,166,.northWest⟩] := by decide
theorem walk_player188 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 188 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨188,target,direction⟩ : WalkEdge)] else []) = [⟨188,189,.east⟩,⟨188,187,.west⟩] := by decide
theorem walk_player189 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 189 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨189,target,direction⟩ : WalkEdge)] else []) = [⟨189,190,.east⟩,⟨189,188,.west⟩] := by decide
theorem walk_player190 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 190 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨190,target,direction⟩ : WalkEdge)] else []) = [⟨190,191,.east⟩,⟨190,189,.west⟩] := by decide
theorem walk_player191 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 191 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨191,target,direction⟩ : WalkEdge)] else []) = [⟨191,192,.east⟩,⟨191,190,.west⟩] := by decide
end NetHack.Sokoban21
