import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0006_0_checked : (List.range' 3072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0006_1_checked : (List.range' 3200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0006_2_checked : (List.range' 3328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0006_3_checked : (List.range' 3456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0006_range (index : Nat) (lower : 3072 ≤ index) (upper : index < 3584) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 3328 then
    if cut : index < 3200 then
      exact segment_sound _ 3072 128 Update0006_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3200 128 Update0006_1_checked index (by omega) (by omega)
  else
    if cut : index < 3456 then
      exact segment_sound _ 3328 128 Update0006_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3456 128 Update0006_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
