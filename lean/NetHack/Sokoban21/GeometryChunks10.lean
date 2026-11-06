/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source131 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 131 direction).map (computedPushEdge 131 direction)) = [] := by decide
theorem push_source134 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 134 direction).map (computedPushEdge 134 direction)) = [⟨134,154,114,114,.north,1,1,true,true⟩,⟨134,114,154,154,.south,1,1,true,true⟩] := by decide
theorem push_source135 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 135 direction).map (computedPushEdge 135 direction)) = [⟨135,155,115,115,.north,1,1,true,true⟩,⟨135,134,136,136,.east,1,1,true,true⟩,⟨135,115,155,155,.south,1,1,true,true⟩,⟨135,136,134,134,.west,1,1,true,true⟩] := by decide
theorem push_source136 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 136 direction).map (computedPushEdge 136 direction)) = [⟨136,156,116,116,.north,1,1,true,true⟩,⟨136,135,137,137,.east,1,1,true,true⟩,⟨136,116,156,156,.south,1,1,true,true⟩,⟨136,137,135,135,.west,1,1,true,true⟩] := by decide
theorem push_source137 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 137 direction).map (computedPushEdge 137 direction)) = [⟨137,157,117,117,.north,1,1,true,true⟩,⟨137,136,138,138,.east,1,1,true,true⟩,⟨137,117,157,157,.south,1,1,true,true⟩,⟨137,138,136,136,.west,1,1,true,true⟩] := by decide
theorem push_source138 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 138 direction).map (computedPushEdge 138 direction)) = [⟨138,158,118,118,.north,1,1,true,true⟩,⟨138,118,158,158,.south,1,1,true,true⟩] := by decide
theorem push_source141 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 141 direction).map (computedPushEdge 141 direction)) = [] := by decide
theorem push_source142 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 142 direction).map (computedPushEdge 142 direction)) = [⟨142,162,122,122,.north,2,13,false,false⟩,⟨142,141,143,143,.east,0,13,false,false⟩,⟨142,122,162,162,.south,0,13,false,false⟩,⟨142,143,141,141,.west,13,13,false,true⟩] := by decide
end NetHack.Sokoban21
