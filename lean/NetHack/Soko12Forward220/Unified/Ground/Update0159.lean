import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0159_0_checked : (List.range' 81408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0159_1_checked : (List.range' 81536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0159_2_checked : (List.range' 81664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0159_3_checked : (List.range' 81792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0159_range (index : Nat) (lower : 81408 ≤ index) (upper : index < 81920) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 81664 then
    if cut : index < 81536 then
      exact segment_sound _ 81408 128 Update0159_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81536 128 Update0159_1_checked index (by omega) (by omega)
  else
    if cut : index < 81792 then
      exact segment_sound _ 81664 128 Update0159_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81792 128 Update0159_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
