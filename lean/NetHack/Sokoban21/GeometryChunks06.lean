/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source87 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 87 direction).map (computedPushEdge 87 direction)) = [⟨87,107,67,67,.north,0,1,false,false⟩,⟨87,67,107,107,.south,1,1,false,false⟩] := by decide
theorem push_source88 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 88 direction).map (computedPushEdge 88 direction)) = [⟨88,108,68,68,.north,1,1,false,false⟩,⟨88,68,108,108,.south,1,1,false,false⟩] := by decide
theorem push_source90 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 90 direction).map (computedPushEdge 90 direction)) = [⟨90,110,70,70,.north,1,1,false,false⟩,⟨90,70,110,110,.south,1,1,false,false⟩] := by decide
theorem push_source92 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 92 direction).map (computedPushEdge 92 direction)) = [⟨92,112,72,72,.north,1,1,true,true⟩,⟨92,72,112,112,.south,1,1,true,true⟩] := by decide
theorem push_source94 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 94 direction).map (computedPushEdge 94 direction)) = [⟨94,114,74,74,.north,1,1,true,true⟩,⟨94,74,114,114,.south,1,1,true,true⟩] := by decide
theorem push_source95 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 95 direction).map (computedPushEdge 95 direction)) = [⟨95,115,75,75,.north,1,1,true,true⟩,⟨95,94,96,96,.east,1,1,true,true⟩,⟨95,75,115,115,.south,1,1,true,true⟩,⟨95,96,94,94,.west,1,1,true,true⟩] := by decide
theorem push_source96 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 96 direction).map (computedPushEdge 96 direction)) = [⟨96,116,76,76,.north,1,1,true,true⟩,⟨96,95,97,97,.east,1,1,true,true⟩,⟨96,76,116,116,.south,1,1,true,true⟩,⟨96,97,95,95,.west,1,1,true,true⟩] := by decide
theorem push_source97 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 97 direction).map (computedPushEdge 97 direction)) = [⟨97,117,77,77,.north,1,1,true,true⟩,⟨97,96,98,98,.east,1,1,true,true⟩,⟨97,77,117,117,.south,1,1,true,true⟩,⟨97,98,96,96,.west,1,1,true,true⟩] := by decide
end NetHack.Sokoban21
