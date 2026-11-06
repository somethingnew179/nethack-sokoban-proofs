/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source64 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 64 direction).map (computedPushEdge 64 direction)) = [⟨64,84,44,44,.north,0,5,false,false⟩,⟨64,44,84,84,.south,5,5,false,true⟩] := by decide
theorem push_source65 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 65 direction).map (computedPushEdge 65 direction)) = [⟨65,85,45,45,.north,2,4,false,false⟩,⟨65,64,66,66,.east,2,4,false,false⟩,⟨65,45,85,85,.south,4,4,false,true⟩,⟨65,66,64,64,.west,0,4,false,false⟩] := by decide
theorem push_source66 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 66 direction).map (computedPushEdge 66 direction)) = [⟨66,65,67,67,.east,2,3,false,false⟩,⟨66,67,65,65,.west,0,3,false,false⟩] := by decide
theorem push_source67 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 67 direction).map (computedPushEdge 67 direction)) = [⟨67,87,47,47,.north,2,2,false,false⟩,⟨67,66,68,68,.east,2,2,false,false⟩,⟨67,47,87,87,.south,2,2,false,false⟩,⟨67,68,66,66,.west,0,2,false,false⟩] := by decide
theorem push_source68 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 68 direction).map (computedPushEdge 68 direction)) = [⟨68,88,48,48,.north,1,1,false,false⟩,⟨68,48,88,88,.south,1,1,false,false⟩] := by decide
theorem push_source70 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 70 direction).map (computedPushEdge 70 direction)) = [⟨70,90,50,50,.north,1,1,false,false⟩,⟨70,50,90,90,.south,1,1,false,false⟩] := by decide
theorem push_source71 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 71 direction).map (computedPushEdge 71 direction)) = [⟨71,70,72,72,.east,1,1,false,true⟩,⟨71,72,70,70,.west,1,1,false,false⟩] := by decide
theorem push_source72 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 72 direction).map (computedPushEdge 72 direction)) = [⟨72,92,52,52,.north,1,1,true,true⟩,⟨72,52,92,92,.south,1,1,true,true⟩] := by decide
end NetHack.Sokoban21
