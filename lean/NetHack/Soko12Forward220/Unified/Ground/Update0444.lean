import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0444_0_checked : (List.range' 227328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0444_1_checked : (List.range' 227456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0444_2_checked : (List.range' 227584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0444_3_checked : (List.range' 227712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0444_range (index : Nat) (lower : 227328 ≤ index) (upper : index < 227840) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 227584 then
    if cut : index < 227456 then
      exact segment_sound _ 227328 128 Update0444_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 227456 128 Update0444_1_checked index (by omega) (by omega)
  else
    if cut : index < 227712 then
      exact segment_sound _ 227584 128 Update0444_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 227712 128 Update0444_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
