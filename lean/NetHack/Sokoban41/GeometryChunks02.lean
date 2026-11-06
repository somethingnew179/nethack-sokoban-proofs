/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source24 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 24 direction).map (computedPushEdge 24 direction)) = [⟨24,23,25,25,.east,1,1,true,true⟩,⟨24,25,23,23,.west,1,1,true,true⟩] := by decide
theorem push_source25 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 25 direction).map (computedPushEdge 25 direction)) = [] := by decide
theorem push_source147 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 147 direction).map (computedPushEdge 147 direction)) = [⟨147,146,148,148,.east,1,18,false,false⟩,⟨147,148,146,146,.west,0,0,false,false⟩] := by decide
theorem push_source148 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 148 direction).map (computedPushEdge 148 direction)) = [⟨148,147,149,149,.east,2,18,false,false⟩,⟨148,149,147,148,.west,1,18,false,false⟩,⟨148,149,147,147,.west,1,18,false,false⟩,⟨148,149,147,146,.west,0,0,false,false⟩,⟨148,149,147,145,.west,0,0,false,false⟩,⟨148,149,147,144,.west,0,0,false,false⟩,⟨148,149,147,143,.west,0,0,false,false⟩,⟨148,149,147,142,.west,0,0,false,false⟩] := by decide
theorem push_source149 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 149 direction).map (computedPushEdge 149 direction)) = [⟨149,148,150,150,.east,2,17,false,false⟩,⟨149,150,148,148,.west,0,17,false,false⟩] := by decide
theorem push_source29 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 29 direction).map (computedPushEdge 29 direction)) = [⟨29,43,15,15,.north,1,1,true,true⟩,⟨29,15,43,43,.south,1,1,true,true⟩] := by decide
theorem push_source30 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 30 direction).map (computedPushEdge 30 direction)) = [⟨30,44,16,16,.north,1,1,false,true⟩,⟨30,29,31,31,.east,1,1,false,false⟩,⟨30,16,44,44,.south,1,1,false,false⟩,⟨30,31,29,29,.west,1,1,false,true⟩] := by decide
theorem push_source31 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 31 direction).map (computedPushEdge 31 direction)) = [⟨31,45,17,17,.north,1,1,false,true⟩,⟨31,30,32,32,.east,0,1,false,false⟩,⟨31,17,45,45,.south,0,1,false,false⟩,⟨31,32,30,30,.west,1,1,false,false⟩] := by decide
end NetHack.Sokoban41
