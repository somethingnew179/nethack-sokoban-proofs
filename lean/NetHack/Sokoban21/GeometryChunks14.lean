/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source190 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 190 direction).map (computedPushEdge 190 direction)) = [⟨190,189,191,191,.east,1,1,false,false⟩,⟨190,191,189,189,.west,1,1,false,false⟩] := by decide
theorem push_source191 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 191 direction).map (computedPushEdge 191 direction)) = [⟨191,190,192,192,.east,1,1,false,false⟩,⟨191,192,190,190,.west,1,1,false,false⟩] := by decide
theorem push_source192 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 192 direction).map (computedPushEdge 192 direction)) = [⟨192,191,193,193,.east,1,1,false,false⟩,⟨192,193,191,191,.west,1,1,false,false⟩] := by decide
theorem push_source193 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 193 direction).map (computedPushEdge 193 direction)) = [⟨193,192,194,194,.east,1,1,false,false⟩,⟨193,194,192,192,.west,1,1,false,false⟩] := by decide
theorem push_source194 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 194 direction).map (computedPushEdge 194 direction)) = [⟨194,193,195,195,.east,1,1,false,false⟩,⟨194,195,193,193,.west,1,1,false,false⟩] := by decide
theorem push_source195 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 195 direction).map (computedPushEdge 195 direction)) = [⟨195,194,196,196,.east,1,1,false,false⟩,⟨195,196,194,194,.west,1,1,false,false⟩] := by decide
theorem push_source196 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 196 direction).map (computedPushEdge 196 direction)) = [⟨196,195,197,197,.east,1,1,false,false⟩,⟨196,197,195,195,.west,1,1,false,false⟩] := by decide
theorem push_source197 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 197 direction).map (computedPushEdge 197 direction)) = [⟨197,196,198,198,.east,20,20,false,true⟩,⟨197,198,196,196,.west,1,1,false,false⟩] := by decide
end NetHack.Sokoban21
