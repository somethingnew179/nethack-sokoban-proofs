/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source121 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 121 direction).map (computedPushEdge 121 direction)) = [⟨121,141,101,101,.north,1,1,true,true⟩,⟨121,101,141,141,.south,1,1,true,true⟩] := by decide
theorem push_source122 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 122 direction).map (computedPushEdge 122 direction)) = [⟨122,142,102,102,.north,2,12,false,false⟩,⟨122,121,123,123,.east,0,12,false,false⟩,⟨122,102,142,142,.south,0,12,false,false⟩,⟨122,123,121,121,.west,12,12,false,true⟩] := by decide
theorem push_source123 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 123 direction).map (computedPushEdge 123 direction)) = [⟨123,143,103,103,.north,13,13,false,true⟩,⟨123,103,143,143,.south,0,13,false,false⟩] := by decide
theorem push_source125 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 125 direction).map (computedPushEdge 125 direction)) = [] := by decide
theorem push_source126 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 126 direction).map (computedPushEdge 126 direction)) = [⟨126,146,106,106,.north,16,16,false,true⟩,⟨126,125,127,127,.east,16,16,false,true⟩,⟨126,106,146,146,.south,0,16,false,false⟩,⟨126,127,125,125,.west,16,16,false,true⟩] := by decide
theorem push_source127 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 127 direction).map (computedPushEdge 127 direction)) = [] := by decide
theorem push_source129 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 129 direction).map (computedPushEdge 129 direction)) = [⟨129,149,109,109,.north,1,1,false,false⟩,⟨129,109,149,149,.south,1,1,false,true⟩] := by decide
theorem push_source130 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 130 direction).map (computedPushEdge 130 direction)) = [⟨130,150,110,110,.north,1,1,false,false⟩,⟨130,129,131,131,.east,1,1,false,true⟩,⟨130,110,150,150,.south,1,1,false,true⟩,⟨130,131,129,129,.west,1,1,false,false⟩] := by decide
end NetHack.Sokoban21
