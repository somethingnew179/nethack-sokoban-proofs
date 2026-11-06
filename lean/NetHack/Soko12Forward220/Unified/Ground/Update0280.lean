import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0280_0_checked : (List.range' 143360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0280_1_checked : (List.range' 143488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0280_2_checked : (List.range' 143616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0280_3_checked : (List.range' 143744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0280_range (index : Nat) (lower : 143360 ≤ index) (upper : index < 143872) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 143616 then
    if cut : index < 143488 then
      exact segment_sound _ 143360 128 Update0280_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 143488 128 Update0280_1_checked index (by omega) (by omega)
  else
    if cut : index < 143744 then
      exact segment_sound _ 143616 128 Update0280_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 143744 128 Update0280_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
