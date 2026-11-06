import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0575_0_checked : (List.range' 294400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0575_1_checked : (List.range' 294528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0575_2_checked : (List.range' 294656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0575_3_checked : (List.range' 294784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0575_range (index : Nat) (lower : 294400 ≤ index) (upper : index < 294912) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 294656 then
    if cut : index < 294528 then
      exact segment_sound _ 294400 128 Update0575_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294528 128 Update0575_1_checked index (by omega) (by omega)
  else
    if cut : index < 294784 then
      exact segment_sound _ 294656 128 Update0575_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294784 128 Update0575_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
