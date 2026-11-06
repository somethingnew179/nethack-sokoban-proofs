import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0097_0_checked : (List.range' 49664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0097_1_checked : (List.range' 49792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0097_2_checked : (List.range' 49920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0097_3_checked : (List.range' 50048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0097_range (index : Nat) (lower : 49664 ≤ index) (upper : index < 50176) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 49920 then
    if cut : index < 49792 then
      exact segment_sound _ 49664 128 Update0097_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49792 128 Update0097_1_checked index (by omega) (by omega)
  else
    if cut : index < 50048 then
      exact segment_sound _ 49920 128 Update0097_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 50048 128 Update0097_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
