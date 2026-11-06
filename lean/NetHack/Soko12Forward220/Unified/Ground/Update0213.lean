import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0213_0_checked : (List.range' 109056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0213_1_checked : (List.range' 109184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0213_2_checked : (List.range' 109312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0213_3_checked : (List.range' 109440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0213_range (index : Nat) (lower : 109056 ≤ index) (upper : index < 109568) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 109312 then
    if cut : index < 109184 then
      exact segment_sound _ 109056 128 Update0213_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109184 128 Update0213_1_checked index (by omega) (by omega)
  else
    if cut : index < 109440 then
      exact segment_sound _ 109312 128 Update0213_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109440 128 Update0213_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
