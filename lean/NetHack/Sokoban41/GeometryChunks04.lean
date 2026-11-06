/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source44 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 44 direction).map (computedPushEdge 44 direction)) = [⟨44,58,30,30,.north,1,1,false,false⟩,⟨44,43,45,45,.east,0,1,false,false⟩,⟨44,30,58,58,.south,1,1,false,true⟩,⟨44,45,43,43,.west,1,1,false,true⟩] := by decide
theorem push_source45 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 45 direction).map (computedPushEdge 45 direction)) = [⟨45,44,46,46,.east,0,2,false,false⟩,⟨45,46,44,44,.west,2,2,false,false⟩] := by decide
theorem push_source46 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 46 direction).map (computedPushEdge 46 direction)) = [⟨46,45,47,47,.east,0,3,false,false⟩,⟨46,47,45,45,.west,2,3,false,false⟩] := by decide
theorem push_source47 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 47 direction).map (computedPushEdge 47 direction)) = [⟨47,46,48,48,.east,0,4,false,false⟩,⟨47,48,46,46,.west,2,4,false,false⟩] := by decide
theorem push_source48 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 48 direction).map (computedPushEdge 48 direction)) = [⟨48,47,49,49,.east,0,5,false,false⟩,⟨48,49,47,47,.west,2,5,false,false⟩] := by decide
theorem push_source49 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 49 direction).map (computedPushEdge 49 direction)) = [⟨49,48,50,50,.east,0,6,false,false⟩,⟨49,50,48,48,.west,2,6,false,false⟩] := by decide
theorem push_source50 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 50 direction).map (computedPushEdge 50 direction)) = [⟨50,49,51,51,.east,0,7,false,false⟩,⟨50,51,49,49,.west,2,7,false,false⟩] := by decide
theorem push_source51 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 51 direction).map (computedPushEdge 51 direction)) = [⟨51,50,52,52,.east,0,8,false,false⟩,⟨51,52,50,50,.west,2,8,false,false⟩] := by decide
end NetHack.Sokoban41
