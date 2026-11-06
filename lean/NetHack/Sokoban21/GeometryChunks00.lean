/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.Rows
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
def reverseRow (player : Cell) : Bool := allDirs.all fun direction =>
  match advance soko2_1.board player direction with
  | none => true
  | some source => decide (advance soko2_1.board source direction.opposite = some player)
theorem push_source21 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 21 direction).map (computedPushEdge 21 direction)) = [] := by decide
theorem push_source22 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 22 direction).map (computedPushEdge 22 direction)) = [⟨22,21,23,23,.east,1,1,true,true⟩,⟨22,23,21,21,.west,1,1,true,true⟩] := by decide
theorem push_source23 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 23 direction).map (computedPushEdge 23 direction)) = [⟨23,22,24,24,.east,1,1,true,true⟩,⟨23,24,22,22,.west,1,1,true,true⟩] := by decide
theorem push_source24 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 24 direction).map (computedPushEdge 24 direction)) = [⟨24,23,25,25,.east,1,1,true,true⟩,⟨24,25,23,23,.west,1,1,true,true⟩] := by decide
theorem push_source25 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 25 direction).map (computedPushEdge 25 direction)) = [⟨25,24,26,26,.east,1,1,true,true⟩,⟨25,26,24,24,.west,1,1,true,true⟩] := by decide
theorem push_source26 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 26 direction).map (computedPushEdge 26 direction)) = [⟨26,25,27,27,.east,1,1,true,true⟩,⟨26,27,25,25,.west,1,1,true,true⟩] := by decide
theorem push_source27 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 27 direction).map (computedPushEdge 27 direction)) = [⟨27,26,28,28,.east,1,1,true,true⟩,⟨27,28,26,26,.west,1,1,true,true⟩] := by decide
theorem push_source28 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko2_1.board 28 direction).map (computedPushEdge 28 direction)) = [] := by decide
end NetHack.Sokoban21
