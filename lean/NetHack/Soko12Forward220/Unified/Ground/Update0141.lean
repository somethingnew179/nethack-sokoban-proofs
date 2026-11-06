import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0141_0_checked : (List.range' 72192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0141_1_checked : (List.range' 72320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0141_2_checked : (List.range' 72448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0141_3_checked : (List.range' 72576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0141_range (index : Nat) (lower : 72192 ≤ index) (upper : index < 72704) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 72448 then
    if cut : index < 72320 then
      exact segment_sound _ 72192 128 Update0141_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 72320 128 Update0141_1_checked index (by omega) (by omega)
  else
    if cut : index < 72576 then
      exact segment_sound _ 72448 128 Update0141_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 72576 128 Update0141_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
