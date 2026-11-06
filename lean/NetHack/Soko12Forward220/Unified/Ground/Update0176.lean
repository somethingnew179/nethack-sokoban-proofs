import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0176_0_checked : (List.range' 90112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0176_1_checked : (List.range' 90240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0176_2_checked : (List.range' 90368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0176_3_checked : (List.range' 90496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0176_range (index : Nat) (lower : 90112 ≤ index) (upper : index < 90624) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 90368 then
    if cut : index < 90240 then
      exact segment_sound _ 90112 128 Update0176_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 90240 128 Update0176_1_checked index (by omega) (by omega)
  else
    if cut : index < 90496 then
      exact segment_sound _ 90368 128 Update0176_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 90496 128 Update0176_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
