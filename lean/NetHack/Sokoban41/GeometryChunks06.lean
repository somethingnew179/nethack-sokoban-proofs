/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source85 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 85 direction).map (computedPushEdge 85 direction)) = [] := by decide
theorem push_source86 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 86 direction).map (computedPushEdge 86 direction)) = [⟨86,85,87,87,.east,0,20,false,false⟩,⟨86,87,85,85,.west,20,20,false,true⟩] := by decide
theorem push_source87 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 87 direction).map (computedPushEdge 87 direction)) = [⟨87,86,88,88,.east,0,0,false,false⟩,⟨87,88,86,86,.west,2,2,false,false⟩] := by decide
theorem push_source88 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 88 direction).map (computedPushEdge 88 direction)) = [⟨88,87,89,89,.east,2,22,false,false⟩,⟨88,89,87,87,.west,2,22,false,false⟩] := by decide
theorem push_source89 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 89 direction).map (computedPushEdge 89 direction)) = [⟨89,88,90,90,.east,21,21,false,true⟩,⟨89,90,88,88,.west,0,0,false,false⟩] := by decide
theorem push_source90 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 90 direction).map (computedPushEdge 90 direction)) = [] := by decide
theorem push_source151 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 151 direction).map (computedPushEdge 151 direction)) = [⟨151,150,152,152,.east,15,15,false,true⟩,⟨151,152,150,150,.west,0,15,false,false⟩] := by decide
theorem push_source92 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 92 direction).map (computedPushEdge 92 direction)) = [] := by decide
end NetHack.Sokoban41
