/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source30 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 30 direction).map (computedPushEdge 30 direction)) = [] := by decide
theorem push_source31 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 31 direction).map (computedPushEdge 31 direction)) = [⟨31,30,32,32,.east,1,1,true,true⟩,⟨31,32,30,30,.west,1,1,true,true⟩] := by decide
theorem push_source32 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 32 direction).map (computedPushEdge 32 direction)) = [] := by decide
theorem push_source34 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 34 direction).map (computedPushEdge 34 direction)) = [] := by decide
theorem push_source35 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 35 direction).map (computedPushEdge 35 direction)) = [⟨35,34,36,36,.east,1,1,true,true⟩,⟨35,36,34,34,.west,1,1,true,true⟩] := by decide
theorem push_source36 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 36 direction).map (computedPushEdge 36 direction)) = [⟨36,35,37,37,.east,1,1,true,true⟩,⟨36,37,35,35,.west,1,1,true,true⟩] := by decide
theorem push_source37 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 37 direction).map (computedPushEdge 37 direction)) = [⟨37,36,38,38,.east,1,1,true,true⟩,⟨37,38,36,36,.west,1,1,true,true⟩] := by decide
theorem push_source38 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 38 direction).map (computedPushEdge 38 direction)) = [] := by decide
end NetHack.Sokoban21
