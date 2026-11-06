import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0338_0_checked : (List.range' 173056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0338_1_checked : (List.range' 173184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0338_2_checked : (List.range' 173312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0338_3_checked : (List.range' 173440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0338_range (index : Nat) (lower : 173056 ≤ index) (upper : index < 173568) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 173312 then
    if cut : index < 173184 then
      exact segment_sound _ 173056 128 Update0338_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 173184 128 Update0338_1_checked index (by omega) (by omega)
  else
    if cut : index < 173440 then
      exact segment_sound _ 173312 128 Update0338_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 173440 128 Update0338_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
