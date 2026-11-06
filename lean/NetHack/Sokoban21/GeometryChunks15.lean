/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source198 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 198 direction).map (computedPushEdge 198 direction)) = [] := by decide
theorem push_source201 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 201 direction).map (computedPushEdge 201 direction)) = [] := by decide
theorem push_source202 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 202 direction).map (computedPushEdge 202 direction)) = [⟨202,201,203,203,.east,1,1,true,true⟩,⟨202,203,201,201,.west,1,1,true,true⟩] := by decide
theorem push_source203 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 203 direction).map (computedPushEdge 203 direction)) = [] := by decide
theorem push_source205 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 205 direction).map (computedPushEdge 205 direction)) = [] := by decide
theorem push_source206 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 206 direction).map (computedPushEdge 206 direction)) = [] := by decide
theorem walk_player21 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 21 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨21,target,direction⟩ : WalkEdge)] else []) = [⟨21,22,.east⟩,⟨21,41,.south⟩,⟨21,42,.southEast⟩] := by decide
theorem walk_player22 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 22 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨22,target,direction⟩ : WalkEdge)] else []) = [⟨22,23,.east⟩,⟨22,42,.south⟩,⟨22,21,.west⟩,⟨22,43,.southEast⟩,⟨22,41,.southWest⟩] := by decide
end NetHack.Sokoban21
