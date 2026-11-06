import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0180_0_checked : (List.range' 92160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0180_1_checked : (List.range' 92288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0180_2_checked : (List.range' 92416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0180_3_checked : (List.range' 92544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0180_range (index : Nat) (lower : 92160 ≤ index) (upper : index < 92672) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 92416 then
    if cut : index < 92288 then
      exact segment_sound _ 92160 128 Update0180_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 92288 128 Update0180_1_checked index (by omega) (by omega)
  else
    if cut : index < 92544 then
      exact segment_sound _ 92416 128 Update0180_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 92544 128 Update0180_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
