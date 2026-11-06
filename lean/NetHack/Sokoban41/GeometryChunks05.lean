/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source52 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 52 direction).map (computedPushEdge 52 direction)) = [⟨52,66,38,38,.north,2,9,false,false⟩,⟨52,51,53,53,.east,9,9,false,true⟩,⟨52,38,66,66,.south,0,9,false,false⟩,⟨52,53,51,51,.west,2,9,false,false⟩] := by decide
theorem push_source53 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 53 direction).map (computedPushEdge 53 direction)) = [⟨53,67,39,39,.north,1,1,true,true⟩,⟨53,39,67,67,.south,1,1,true,true⟩] := by decide
theorem push_source57 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 57 direction).map (computedPushEdge 57 direction)) = [] := by decide
theorem push_source58 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 58 direction).map (computedPushEdge 58 direction)) = [] := by decide
theorem push_source62 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 62 direction).map (computedPushEdge 62 direction)) = [] := by decide
theorem push_source66 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 66 direction).map (computedPushEdge 66 direction)) = [⟨66,80,52,52,.north,2,10,false,false⟩,⟨66,52,80,80,.south,0,10,false,false⟩] := by decide
theorem push_source67 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 67 direction).map (computedPushEdge 67 direction)) = [] := by decide
theorem push_source80 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 80 direction).map (computedPushEdge 80 direction)) = [⟨80,94,66,66,.north,2,11,false,false⟩,⟨80,66,94,94,.south,0,11,false,false⟩] := by decide
end NetHack.Sokoban41
