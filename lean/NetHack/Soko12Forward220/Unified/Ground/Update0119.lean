import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0119_0_checked : (List.range' 60928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0119_1_checked : (List.range' 61056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0119_2_checked : (List.range' 61184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0119_3_checked : (List.range' 61312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0119_range (index : Nat) (lower : 60928 ≤ index) (upper : index < 61440) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 61184 then
    if cut : index < 61056 then
      exact segment_sound _ 60928 128 Update0119_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 61056 128 Update0119_1_checked index (by omega) (by omega)
  else
    if cut : index < 61312 then
      exact segment_sound _ 61184 128 Update0119_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 61312 128 Update0119_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
