/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source93 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 93 direction).map (computedPushEdge 93 direction)) = [⟨93,92,94,94,.east,0,11,false,false⟩,⟨93,94,92,92,.west,11,11,false,true⟩] := by decide
theorem push_source94 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 94 direction).map (computedPushEdge 94 direction)) = [⟨94,108,80,80,.north,2,12,false,false⟩,⟨94,93,95,95,.east,2,12,false,false⟩,⟨94,80,108,108,.south,0,12,false,false⟩,⟨94,95,93,93,.west,2,12,false,false⟩] := by decide
theorem push_source95 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 95 direction).map (computedPushEdge 95 direction)) = [⟨95,94,96,96,.east,11,11,false,true⟩,⟨95,96,94,94,.west,0,11,false,false⟩] := by decide
theorem push_source96 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 96 direction).map (computedPushEdge 96 direction)) = [] := by decide
theorem push_source99 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 99 direction).map (computedPushEdge 99 direction)) = [] := by decide
theorem push_source100 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 100 direction).map (computedPushEdge 100 direction)) = [⟨100,114,86,86,.north,1,1,false,false⟩,⟨100,86,114,114,.south,1,1,false,false⟩] := by decide
theorem push_source106 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 106 direction).map (computedPushEdge 106 direction)) = [⟨106,120,92,92,.north,15,15,false,true⟩,⟨106,92,120,120,.south,0,15,false,false⟩] := by decide
theorem push_source107 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 107 direction).map (computedPushEdge 107 direction)) = [⟨107,121,93,93,.north,4,14,false,false⟩,⟨107,106,108,108,.east,2,14,false,false⟩,⟨107,93,121,121,.south,0,14,false,false⟩,⟨107,108,106,106,.west,0,14,false,false⟩] := by decide
end NetHack.Sokoban41
