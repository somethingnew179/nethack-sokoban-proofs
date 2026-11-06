import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0525_0_checked : (List.range' 268800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0525_1_checked : (List.range' 268928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0525_2_checked : (List.range' 269056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0525_3_checked : (List.range' 269184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0525_range (index : Nat) (lower : 268800 ≤ index) (upper : index < 269312) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 269056 then
    if cut : index < 268928 then
      exact segment_sound _ 268800 128 Update0525_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 268928 128 Update0525_1_checked index (by omega) (by omega)
  else
    if cut : index < 269184 then
      exact segment_sound _ 269056 128 Update0525_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 269184 128 Update0525_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
