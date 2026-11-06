/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source182 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 182 direction).map (computedPushEdge 182 direction)) = [⟨182,202,162,162,.north,2,15,false,false⟩,⟨182,181,183,183,.east,0,15,false,false⟩,⟨182,162,202,202,.south,15,15,false,true⟩,⟨182,183,181,181,.west,15,15,false,true⟩] := by decide
theorem push_source183 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 183 direction).map (computedPushEdge 183 direction)) = [⟨183,203,163,163,.north,2,16,false,false⟩,⟨183,182,184,184,.east,0,16,false,false⟩,⟨183,163,203,203,.south,16,16,false,true⟩,⟨183,184,182,182,.west,2,16,false,false⟩] := by decide
theorem push_source184 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 184 direction).map (computedPushEdge 184 direction)) = [⟨184,183,185,185,.east,0,17,false,false⟩,⟨184,185,183,183,.west,2,17,false,false⟩] := by decide
theorem push_source185 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 185 direction).map (computedPushEdge 185 direction)) = [⟨185,205,165,165,.north,2,18,false,false⟩,⟨185,184,186,186,.east,0,18,false,false⟩,⟨185,165,205,205,.south,18,18,false,true⟩,⟨185,186,184,184,.west,2,18,false,false⟩] := by decide
theorem push_source186 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 186 direction).map (computedPushEdge 186 direction)) = [⟨186,206,166,166,.north,2,19,false,false⟩,⟨186,185,187,186,.east,1,19,false,false⟩,⟨186,185,187,187,.east,1,19,false,false⟩,⟨186,185,187,188,.east,0,0,false,false⟩,⟨186,185,187,189,.east,0,0,false,false⟩,⟨186,185,187,190,.east,0,0,false,false⟩,⟨186,185,187,191,.east,0,0,false,false⟩,⟨186,185,187,192,.east,0,0,false,false⟩,⟨186,185,187,193,.east,0,0,false,false⟩,⟨186,185,187,194,.east,0,0,false,false⟩,⟨186,185,187,195,.east,0,0,false,false⟩,⟨186,185,187,196,.east,0,0,false,false⟩,⟨186,185,187,197,.east,0,0,false,false⟩,⟨186,185,187,198,.east,19,19,false,true⟩,⟨186,166,206,206,.south,19,19,false,true⟩,⟨186,187,185,185,.west,2,19,false,false⟩] := by decide
theorem push_source187 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 187 direction).map (computedPushEdge 187 direction)) = [⟨187,186,188,188,.east,0,0,false,false⟩,⟨187,188,186,186,.west,1,19,false,false⟩] := by decide
theorem push_source188 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 188 direction).map (computedPushEdge 188 direction)) = [⟨188,187,189,189,.east,1,1,false,false⟩,⟨188,189,187,188,.west,1,1,false,false⟩,⟨188,189,187,187,.west,2,20,false,false⟩,⟨188,189,187,186,.west,2,20,false,false⟩,⟨188,189,187,185,.west,3,20,false,false⟩,⟨188,189,187,184,.west,4,20,false,false⟩,⟨188,189,187,183,.west,5,20,false,false⟩,⟨188,189,187,182,.west,6,20,false,false⟩,⟨188,189,187,181,.west,20,20,false,true⟩] := by decide
theorem push_source189 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 189 direction).map (computedPushEdge 189 direction)) = [⟨189,188,190,190,.east,1,1,false,false⟩,⟨189,190,188,188,.west,1,1,false,false⟩] := by decide
end NetHack.Sokoban21
