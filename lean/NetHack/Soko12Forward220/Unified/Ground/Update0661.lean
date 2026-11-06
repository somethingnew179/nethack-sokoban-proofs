import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0661_0_checked : (List.range' 338432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0661_1_checked : (List.range' 338560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0661_2_checked : (List.range' 338688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0661_3_checked : (List.range' 338816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0661_range (index : Nat) (lower : 338432 ≤ index) (upper : index < 338944) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 338688 then
    if cut : index < 338560 then
      exact segment_sound _ 338432 128 Update0661_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 338560 128 Update0661_1_checked index (by omega) (by omega)
  else
    if cut : index < 338816 then
      exact segment_sound _ 338688 128 Update0661_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 338816 128 Update0661_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
