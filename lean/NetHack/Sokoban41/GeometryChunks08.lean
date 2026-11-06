/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source108 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 108 direction).map (computedPushEdge 108 direction)) = [⟨108,122,94,94,.north,2,13,false,false⟩,⟨108,107,109,109,.east,2,13,false,false⟩,⟨108,94,122,122,.south,0,13,false,false⟩,⟨108,109,107,107,.west,0,13,false,false⟩] := by decide
theorem push_source109 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 109 direction).map (computedPushEdge 109 direction)) = [⟨109,123,95,95,.north,2,12,false,false⟩,⟨109,108,110,110,.east,12,12,false,true⟩,⟨109,95,123,123,.south,0,12,false,false⟩,⟨109,110,108,108,.west,0,12,false,false⟩] := by decide
theorem push_source110 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 110 direction).map (computedPushEdge 110 direction)) = [⟨110,124,96,96,.north,1,1,true,true⟩,⟨110,96,124,124,.south,1,1,true,true⟩] := by decide
theorem push_source114 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 114 direction).map (computedPushEdge 114 direction)) = [⟨114,128,100,100,.north,1,1,false,false⟩,⟨114,100,128,114,.south,1,1,false,false⟩,⟨114,100,128,128,.south,2,20,false,false⟩,⟨114,100,128,142,.south,2,2,false,false⟩,⟨114,100,128,156,.south,20,20,false,true⟩] := by decide
theorem push_source150 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 150 direction).map (computedPushEdge 150 direction)) = [⟨150,149,151,151,.east,2,16,false,false⟩,⟨150,151,149,149,.west,0,16,false,false⟩] := by decide
theorem push_source120 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 120 direction).map (computedPushEdge 120 direction)) = [⟨120,134,106,106,.north,2,16,false,false⟩,⟨120,106,134,134,.south,0,16,false,false⟩] := by decide
theorem push_source121 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 121 direction).map (computedPushEdge 121 direction)) = [⟨121,135,107,107,.north,2,15,false,false⟩,⟨121,120,122,122,.east,2,15,false,false⟩,⟨121,107,135,135,.south,0,15,false,false⟩,⟨121,122,120,120,.west,0,15,false,false⟩] := by decide
theorem push_source122 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 122 direction).map (computedPushEdge 122 direction)) = [⟨122,136,108,108,.north,2,14,false,false⟩,⟨122,121,123,123,.east,2,14,false,false⟩,⟨122,108,136,136,.south,0,14,false,false⟩,⟨122,123,121,121,.west,0,14,false,false⟩] := by decide
end NetHack.Sokoban41
