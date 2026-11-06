import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0303_0_checked : (List.range' 155136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0303_1_checked : (List.range' 155264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0303_2_checked : (List.range' 155392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0303_3_checked : (List.range' 155520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0303_range (index : Nat) (lower : 155136 ≤ index) (upper : index < 155648) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 155392 then
    if cut : index < 155264 then
      exact segment_sound _ 155136 128 Update0303_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155264 128 Update0303_1_checked index (by omega) (by omega)
  else
    if cut : index < 155520 then
      exact segment_sound _ 155392 128 Update0303_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155520 128 Update0303_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
