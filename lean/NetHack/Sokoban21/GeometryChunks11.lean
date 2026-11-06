/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source143 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 143 direction).map (computedPushEdge 143 direction)) = [⟨143,163,123,123,.north,2,14,false,false⟩,⟨143,123,163,163,.south,0,14,false,false⟩] := by decide
theorem push_source145 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 145 direction).map (computedPushEdge 145 direction)) = [⟨145,165,125,125,.north,16,16,false,true⟩,⟨145,125,165,165,.south,0,16,false,false⟩] := by decide
theorem push_source146 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 146 direction).map (computedPushEdge 146 direction)) = [⟨146,166,126,126,.north,2,17,false,false⟩,⟨146,126,166,166,.south,0,17,false,false⟩] := by decide
theorem push_source148 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 148 direction).map (computedPushEdge 148 direction)) = [] := by decide
theorem push_source149 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 149 direction).map (computedPushEdge 149 direction)) = [⟨149,148,150,150,.east,1,1,true,true⟩,⟨149,150,148,148,.west,1,1,true,true⟩] := by decide
theorem push_source150 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 150 direction).map (computedPushEdge 150 direction)) = [] := by decide
theorem push_source154 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 154 direction).map (computedPushEdge 154 direction)) = [] := by decide
theorem push_source155 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 155 direction).map (computedPushEdge 155 direction)) = [⟨155,154,156,156,.east,1,1,true,true⟩,⟨155,156,154,154,.west,1,1,true,true⟩] := by decide
end NetHack.Sokoban21
