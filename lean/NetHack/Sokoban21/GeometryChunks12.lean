/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source156 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 156 direction).map (computedPushEdge 156 direction)) = [⟨156,155,157,157,.east,1,1,true,true⟩,⟨156,157,155,155,.west,1,1,true,true⟩] := by decide
theorem push_source157 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 157 direction).map (computedPushEdge 157 direction)) = [⟨157,156,158,158,.east,1,1,true,true⟩,⟨157,158,156,156,.west,1,1,true,true⟩] := by decide
theorem push_source158 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 158 direction).map (computedPushEdge 158 direction)) = [] := by decide
theorem push_source162 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 162 direction).map (computedPushEdge 162 direction)) = [⟨162,182,142,142,.north,2,14,false,false⟩,⟨162,142,182,182,.south,0,14,false,false⟩] := by decide
theorem push_source163 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 163 direction).map (computedPushEdge 163 direction)) = [⟨163,183,143,143,.north,2,15,false,false⟩,⟨163,143,183,183,.south,0,15,false,false⟩] := by decide
theorem push_source165 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 165 direction).map (computedPushEdge 165 direction)) = [⟨165,185,145,145,.north,2,17,false,false⟩,⟨165,145,185,185,.south,0,17,false,false⟩] := by decide
theorem push_source166 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 166 direction).map (computedPushEdge 166 direction)) = [⟨166,186,146,146,.north,2,18,false,false⟩,⟨166,146,186,186,.south,0,18,false,false⟩] := by decide
theorem push_source181 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 181 direction).map (computedPushEdge 181 direction)) = [] := by decide
end NetHack.Sokoban21
