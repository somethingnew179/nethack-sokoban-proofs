import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0659_0_checked : (List.range' 337408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0659_1_checked : (List.range' 337536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0659_2_checked : (List.range' 337664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0659_3_checked : (List.range' 337792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0659_range (index : Nat) (lower : 337408 ≤ index) (upper : index < 337920) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 337664 then
    if cut : index < 337536 then
      exact segment_sound _ 337408 128 Update0659_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 337536 128 Update0659_1_checked index (by omega) (by omega)
  else
    if cut : index < 337792 then
      exact segment_sound _ 337664 128 Update0659_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 337792 128 Update0659_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
