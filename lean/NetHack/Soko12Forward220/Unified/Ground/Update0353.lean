import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0353_0_checked : (List.range' 180736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0353_1_checked : (List.range' 180864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0353_2_checked : (List.range' 180992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0353_3_checked : (List.range' 181120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0353_range (index : Nat) (lower : 180736 ≤ index) (upper : index < 181248) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 180992 then
    if cut : index < 180864 then
      exact segment_sound _ 180736 128 Update0353_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180864 128 Update0353_1_checked index (by omega) (by omega)
  else
    if cut : index < 181120 then
      exact segment_sound _ 180992 128 Update0353_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 181120 128 Update0353_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
