/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source32 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 32 direction).map (computedPushEdge 32 direction)) = [⟨32,46,18,18,.north,2,2,false,true⟩,⟨32,18,46,46,.south,0,2,false,false⟩] := by decide
theorem push_source152 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 152 direction).map (computedPushEdge 152 direction)) = [] := by decide
theorem push_source156 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 156 direction).map (computedPushEdge 156 direction)) = [] := by decide
theorem push_source157 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 157 direction).map (computedPushEdge 157 direction)) = [] := by decide
theorem push_source37 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 37 direction).map (computedPushEdge 37 direction)) = [⟨37,51,23,23,.north,7,7,false,true⟩,⟨37,23,51,51,.south,0,7,false,false⟩] := by decide
theorem push_source38 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 38 direction).map (computedPushEdge 38 direction)) = [⟨38,52,24,24,.north,8,8,false,true⟩,⟨38,37,39,39,.east,8,8,false,true⟩,⟨38,24,52,52,.south,0,8,false,false⟩,⟨38,39,37,37,.west,2,8,false,false⟩] := by decide
theorem push_source39 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 39 direction).map (computedPushEdge 39 direction)) = [⟨39,53,25,25,.north,1,1,true,true⟩,⟨39,25,53,53,.south,1,1,true,true⟩] := by decide
theorem push_source43 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 43 direction).map (computedPushEdge 43 direction)) = [⟨43,57,29,29,.north,1,1,true,true⟩,⟨43,29,57,57,.south,1,1,true,true⟩] := by decide
end NetHack.Sokoban41
