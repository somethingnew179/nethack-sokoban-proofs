import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0059_0_checked : (List.range' 30208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0059_1_checked : (List.range' 30336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0059_2_checked : (List.range' 30464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0059_3_checked : (List.range' 30592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0059_range (index : Nat) (lower : 30208 ≤ index) (upper : index < 30720) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 30464 then
    if cut : index < 30336 then
      exact segment_sound _ 30208 128 Update0059_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 30336 128 Update0059_1_checked index (by omega) (by omega)
  else
    if cut : index < 30592 then
      exact segment_sound _ 30464 128 Update0059_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 30592 128 Update0059_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
