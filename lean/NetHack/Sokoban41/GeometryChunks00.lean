/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Rows
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source128 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 128 direction).map (computedPushEdge 128 direction)) = [⟨128,142,114,114,.north,0,0,false,false⟩,⟨128,114,142,142,.south,1,1,false,false⟩] := by decide
theorem push_source134 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 134 direction).map (computedPushEdge 134 direction)) = [⟨134,148,120,120,.north,2,17,false,false⟩,⟨134,120,148,148,.south,0,17,false,false⟩] := by decide
theorem push_source135 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 135 direction).map (computedPushEdge 135 direction)) = [⟨135,149,121,121,.north,2,16,false,false⟩,⟨135,134,136,136,.east,2,16,false,false⟩,⟨135,121,149,149,.south,0,16,false,false⟩,⟨135,136,134,134,.west,0,16,false,false⟩] := by decide
theorem push_source136 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 136 direction).map (computedPushEdge 136 direction)) = [⟨136,150,122,122,.north,2,15,false,false⟩,⟨136,135,137,137,.east,2,15,false,false⟩,⟨136,122,150,150,.south,0,15,false,false⟩,⟨136,137,135,135,.west,0,15,false,false⟩] := by decide
theorem push_source137 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 137 direction).map (computedPushEdge 137 direction)) = [⟨137,151,123,123,.north,2,14,false,false⟩,⟨137,136,138,138,.east,14,14,false,true⟩,⟨137,123,151,151,.south,0,14,false,false⟩,⟨137,138,136,136,.west,0,14,false,false⟩] := by decide
theorem push_source138 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 138 direction).map (computedPushEdge 138 direction)) = [⟨138,152,124,124,.north,1,1,true,true⟩,⟨138,124,152,152,.south,1,1,true,true⟩] := by decide
theorem push_source142 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 142 direction).map (computedPushEdge 142 direction)) = [⟨142,156,128,142,.north,1,1,false,false⟩,⟨142,156,128,128,.north,1,19,false,false⟩,⟨142,156,128,114,.north,0,0,false,false⟩,⟨142,156,128,100,.north,0,0,false,false⟩,⟨142,156,128,86,.north,0,0,false,false⟩,⟨142,128,156,156,.south,19,19,false,true⟩] := by decide
theorem push_source15 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 15 direction).map (computedPushEdge 15 direction)) = [] := by decide
end NetHack.Sokoban41
