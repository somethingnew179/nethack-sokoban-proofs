/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source74 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 74 direction).map (computedPushEdge 74 direction)) = [⟨74,94,54,54,.north,1,1,true,true⟩,⟨74,54,94,94,.south,1,1,true,true⟩] := by decide
theorem push_source75 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 75 direction).map (computedPushEdge 75 direction)) = [⟨75,95,55,55,.north,1,1,true,true⟩,⟨75,74,76,76,.east,1,1,true,true⟩,⟨75,55,95,95,.south,1,1,true,true⟩,⟨75,76,74,74,.west,1,1,true,true⟩] := by decide
theorem push_source76 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 76 direction).map (computedPushEdge 76 direction)) = [⟨76,96,56,56,.north,1,1,true,true⟩,⟨76,75,77,77,.east,1,1,true,true⟩,⟨76,56,96,96,.south,1,1,true,true⟩,⟨76,77,75,75,.west,1,1,true,true⟩] := by decide
theorem push_source77 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 77 direction).map (computedPushEdge 77 direction)) = [⟨77,97,57,57,.north,1,1,true,true⟩,⟨77,76,78,78,.east,1,1,true,true⟩,⟨77,57,97,97,.south,1,1,true,true⟩,⟨77,78,76,76,.west,1,1,true,true⟩] := by decide
theorem push_source78 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 78 direction).map (computedPushEdge 78 direction)) = [⟨78,98,58,58,.north,1,1,true,true⟩,⟨78,58,98,98,.south,1,1,true,true⟩] := by decide
theorem push_source82 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 82 direction).map (computedPushEdge 82 direction)) = [⟨82,102,62,62,.north,2,10,false,false⟩,⟨82,62,102,102,.south,0,10,false,false⟩] := by decide
theorem push_source84 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 84 direction).map (computedPushEdge 84 direction)) = [] := by decide
theorem push_source85 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 85 direction).map (computedPushEdge 85 direction)) = [] := by decide
end NetHack.Sokoban21
