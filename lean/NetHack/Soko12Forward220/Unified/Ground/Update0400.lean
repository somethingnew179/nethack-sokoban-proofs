import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0400_0_checked : (List.range' 204800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0400_1_checked : (List.range' 204928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0400_2_checked : (List.range' 205056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0400_3_checked : (List.range' 205184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0400_range (index : Nat) (lower : 204800 ≤ index) (upper : index < 205312) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 205056 then
    if cut : index < 204928 then
      exact segment_sound _ 204800 128 Update0400_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 204928 128 Update0400_1_checked index (by omega) (by omega)
  else
    if cut : index < 205184 then
      exact segment_sound _ 205056 128 Update0400_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 205184 128 Update0400_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
