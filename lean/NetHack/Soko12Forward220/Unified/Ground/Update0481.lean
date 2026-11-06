import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0481_0_checked : (List.range' 246272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0481_1_checked : (List.range' 246400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0481_2_checked : (List.range' 246528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0481_3_checked : (List.range' 246656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0481_range (index : Nat) (lower : 246272 ≤ index) (upper : index < 246784) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 246528 then
    if cut : index < 246400 then
      exact segment_sound _ 246272 128 Update0481_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246400 128 Update0481_1_checked index (by omega) (by omega)
  else
    if cut : index < 246656 then
      exact segment_sound _ 246528 128 Update0481_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246656 128 Update0481_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
