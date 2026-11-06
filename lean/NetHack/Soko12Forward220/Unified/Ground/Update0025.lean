import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0025_0_checked : (List.range' 12800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0025_1_checked : (List.range' 12928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0025_2_checked : (List.range' 13056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0025_3_checked : (List.range' 13184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0025_range (index : Nat) (lower : 12800 ≤ index) (upper : index < 13312) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 13056 then
    if cut : index < 12928 then
      exact segment_sound _ 12800 128 Update0025_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12928 128 Update0025_1_checked index (by omega) (by omega)
  else
    if cut : index < 13184 then
      exact segment_sound _ 13056 128 Update0025_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 13184 128 Update0025_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
