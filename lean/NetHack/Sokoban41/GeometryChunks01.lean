/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source16 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 16 direction).map (computedPushEdge 16 direction)) = [⟨16,15,17,17,.east,1,1,true,true⟩,⟨16,17,15,15,.west,1,1,true,true⟩] := by decide
theorem push_source17 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 17 direction).map (computedPushEdge 17 direction)) = [⟨17,16,18,18,.east,1,1,true,true⟩,⟨17,18,16,16,.west,1,1,true,true⟩] := by decide
theorem push_source18 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 18 direction).map (computedPushEdge 18 direction)) = [] := by decide
theorem push_source143 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 143 direction).map (computedPushEdge 143 direction)) = [⟨143,142,144,144,.east,1,1,false,false⟩,⟨143,144,142,142,.west,1,1,false,false⟩] := by decide
theorem push_source144 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 144 direction).map (computedPushEdge 144 direction)) = [⟨144,143,145,145,.east,1,1,false,false⟩,⟨144,145,143,143,.west,1,1,false,false⟩] := by decide
theorem push_source145 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 145 direction).map (computedPushEdge 145 direction)) = [⟨145,144,146,146,.east,1,1,false,false⟩,⟨145,146,144,144,.west,1,1,false,false⟩] := by decide
theorem push_source146 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 146 direction).map (computedPushEdge 146 direction)) = [⟨146,145,147,146,.east,1,1,false,false⟩,⟨146,145,147,147,.east,2,19,false,false⟩,⟨146,145,147,148,.east,2,19,false,false⟩,⟨146,145,147,149,.east,3,19,false,false⟩,⟨146,145,147,150,.east,4,19,false,false⟩,⟨146,145,147,151,.east,5,19,false,false⟩,⟨146,145,147,152,.east,19,19,false,true⟩,⟨146,147,145,145,.west,1,1,false,false⟩] := by decide
theorem push_source23 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 23 direction).map (computedPushEdge 23 direction)) = [] := by decide
end NetHack.Sokoban41
