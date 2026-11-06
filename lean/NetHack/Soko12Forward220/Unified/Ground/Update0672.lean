import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0672_0_checked : (List.range' 344064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0672_1_checked : (List.range' 344192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0672_2_checked : (List.range' 344320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0672_3_checked : (List.range' 344448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0672_range (index : Nat) (lower : 344064 ≤ index) (upper : index < 344576) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 344320 then
    if cut : index < 344192 then
      exact segment_sound _ 344064 128 Update0672_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 344192 128 Update0672_1_checked index (by omega) (by omega)
  else
    if cut : index < 344448 then
      exact segment_sound _ 344320 128 Update0672_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 344448 128 Update0672_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
