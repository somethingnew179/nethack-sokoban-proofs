/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem push_source52 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 52 direction).map (computedPushEdge 52 direction)) = [⟨52,72,32,32,.north,1,1,true,true⟩,⟨52,32,72,72,.south,1,1,true,true⟩] := by decide
theorem push_source54 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 54 direction).map (computedPushEdge 54 direction)) = [⟨54,74,34,34,.north,1,1,true,true⟩,⟨54,34,74,74,.south,1,1,true,true⟩] := by decide
theorem push_source55 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 55 direction).map (computedPushEdge 55 direction)) = [⟨55,75,35,35,.north,1,1,true,true⟩,⟨55,54,56,56,.east,1,1,true,true⟩,⟨55,35,75,75,.south,1,1,true,true⟩,⟨55,56,54,54,.west,1,1,true,true⟩] := by decide
theorem push_source56 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 56 direction).map (computedPushEdge 56 direction)) = [⟨56,76,36,36,.north,1,1,true,true⟩,⟨56,55,57,57,.east,1,1,true,true⟩,⟨56,36,76,76,.south,1,1,true,true⟩,⟨56,57,55,55,.west,1,1,true,true⟩] := by decide
theorem push_source57 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 57 direction).map (computedPushEdge 57 direction)) = [⟨57,77,37,37,.north,1,1,true,true⟩,⟨57,56,58,58,.east,1,1,true,true⟩,⟨57,37,77,77,.south,1,1,true,true⟩,⟨57,58,56,56,.west,1,1,true,true⟩] := by decide
theorem push_source58 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 58 direction).map (computedPushEdge 58 direction)) = [⟨58,78,38,38,.north,1,1,true,true⟩,⟨58,38,78,78,.south,1,1,true,true⟩] := by decide
theorem push_source61 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 61 direction).map (computedPushEdge 61 direction)) = [] := by decide
theorem push_source62 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 62 direction).map (computedPushEdge 62 direction)) = [⟨62,82,42,42,.north,2,9,false,false⟩,⟨62,42,82,82,.south,0,9,false,false⟩] := by decide
end NetHack.Sokoban21
