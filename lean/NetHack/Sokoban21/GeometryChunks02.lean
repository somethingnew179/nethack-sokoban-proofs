/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source41 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 41 direction).map (computedPushEdge 41 direction)) = [⟨41,61,21,21,.north,1,1,true,true⟩,⟨41,21,61,61,.south,1,1,true,true⟩] := by decide
theorem push_source42 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 42 direction).map (computedPushEdge 42 direction)) = [⟨42,62,22,22,.north,8,8,false,true⟩,⟨42,41,43,43,.east,2,8,false,false⟩,⟨42,22,62,62,.south,0,8,false,false⟩,⟨42,43,41,41,.west,8,8,false,true⟩] := by decide
theorem push_source43 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 43 direction).map (computedPushEdge 43 direction)) = [⟨43,42,44,44,.east,2,7,false,false⟩,⟨43,44,42,42,.west,0,7,false,false⟩] := by decide
theorem push_source44 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 44 direction).map (computedPushEdge 44 direction)) = [⟨44,64,24,24,.north,6,6,false,true⟩,⟨44,43,45,45,.east,4,6,false,false⟩,⟨44,24,64,64,.south,2,6,false,false⟩,⟨44,45,43,43,.west,0,6,false,false⟩] := by decide
theorem push_source45 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 45 direction).map (computedPushEdge 45 direction)) = [⟨45,65,25,25,.north,3,3,false,true⟩,⟨45,25,65,65,.south,0,3,false,false⟩] := by decide
theorem push_source47 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 47 direction).map (computedPushEdge 47 direction)) = [⟨47,67,27,27,.north,1,1,false,true⟩,⟨47,27,67,67,.south,0,1,false,false⟩] := by decide
theorem push_source48 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 48 direction).map (computedPushEdge 48 direction)) = [⟨48,68,28,28,.north,1,1,false,true⟩,⟨48,28,68,68,.south,1,1,false,false⟩] := by decide
theorem push_source50 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 50 direction).map (computedPushEdge 50 direction)) = [⟨50,70,30,30,.north,1,1,false,true⟩,⟨50,30,70,70,.south,1,1,false,false⟩] := by decide
end NetHack.Sokoban21
