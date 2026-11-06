import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0104_0_checked : (List.range' 53248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0104_1_checked : (List.range' 53376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0104_2_checked : (List.range' 53504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0104_3_checked : (List.range' 53632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0104_range (index : Nat) (lower : 53248 ≤ index) (upper : index < 53760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 53504 then
    if cut : index < 53376 then
      exact segment_sound _ 53248 128 Update0104_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 53376 128 Update0104_1_checked index (by omega) (by omega)
  else
    if cut : index < 53632 then
      exact segment_sound _ 53504 128 Update0104_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 53632 128 Update0104_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
