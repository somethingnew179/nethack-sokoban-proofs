/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source98 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 98 direction).map (computedPushEdge 98 direction)) = [⟨98,118,78,78,.north,1,1,true,true⟩,⟨98,78,118,118,.south,1,1,true,true⟩] := by decide
theorem push_source101 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 101 direction).map (computedPushEdge 101 direction)) = [] := by decide
theorem push_source102 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 102 direction).map (computedPushEdge 102 direction)) = [⟨102,122,82,82,.north,2,11,false,false⟩,⟨102,101,103,103,.east,11,11,false,true⟩,⟨102,82,122,122,.south,0,11,false,false⟩,⟨102,103,101,101,.west,11,11,false,true⟩] := by decide
theorem push_source103 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 103 direction).map (computedPushEdge 103 direction)) = [] := by decide
theorem push_source106 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 106 direction).map (computedPushEdge 106 direction)) = [] := by decide
theorem push_source107 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 107 direction).map (computedPushEdge 107 direction)) = [⟨107,127,87,87,.north,1,1,false,false⟩,⟨107,106,108,108,.east,1,1,false,false⟩,⟨107,87,127,127,.south,1,1,false,true⟩,⟨107,108,106,106,.west,1,1,false,true⟩] := by decide
theorem push_source108 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 108 direction).map (computedPushEdge 108 direction)) = [⟨108,107,109,109,.east,1,1,false,false⟩,⟨108,109,107,107,.west,1,1,false,false⟩] := by decide
theorem push_source109 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 109 direction).map (computedPushEdge 109 direction)) = [⟨109,108,110,110,.east,1,1,false,false⟩,⟨109,110,108,108,.west,1,1,false,false⟩] := by decide
end NetHack.Sokoban21
