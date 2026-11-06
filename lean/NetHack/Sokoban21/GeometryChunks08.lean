/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source110 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 110 direction).map (computedPushEdge 110 direction)) = [⟨110,130,90,90,.north,1,1,false,false⟩,⟨110,109,111,111,.east,1,1,false,false⟩,⟨110,90,130,130,.south,1,1,false,false⟩,⟨110,111,109,109,.west,1,1,false,false⟩] := by decide
theorem push_source111 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 111 direction).map (computedPushEdge 111 direction)) = [⟨111,110,112,112,.east,1,1,false,true⟩,⟨111,112,110,110,.west,1,1,false,false⟩] := by decide
theorem push_source112 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 112 direction).map (computedPushEdge 112 direction)) = [] := by decide
theorem push_source114 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 114 direction).map (computedPushEdge 114 direction)) = [⟨114,134,94,94,.north,1,1,true,true⟩,⟨114,94,134,134,.south,1,1,true,true⟩] := by decide
theorem push_source115 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 115 direction).map (computedPushEdge 115 direction)) = [⟨115,135,95,95,.north,1,1,true,true⟩,⟨115,114,116,116,.east,1,1,true,true⟩,⟨115,95,135,135,.south,1,1,true,true⟩,⟨115,116,114,114,.west,1,1,true,true⟩] := by decide
theorem push_source116 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 116 direction).map (computedPushEdge 116 direction)) = [⟨116,136,96,96,.north,1,1,true,true⟩,⟨116,115,117,117,.east,1,1,true,true⟩,⟨116,96,136,136,.south,1,1,true,true⟩,⟨116,117,115,115,.west,1,1,true,true⟩] := by decide
theorem push_source117 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 117 direction).map (computedPushEdge 117 direction)) = [⟨117,137,97,97,.north,1,1,true,true⟩,⟨117,116,118,118,.east,1,1,true,true⟩,⟨117,97,137,137,.south,1,1,true,true⟩,⟨117,118,116,116,.west,1,1,true,true⟩] := by decide
theorem push_source118 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 118 direction).map (computedPushEdge 118 direction)) = [⟨118,138,98,98,.north,1,1,true,true⟩,⟨118,98,138,138,.south,1,1,true,true⟩] := by decide
end NetHack.Sokoban21
