import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0559_0_checked : (List.range' 286208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0559_1_checked : (List.range' 286336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0559_2_checked : (List.range' 286464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0559_3_checked : (List.range' 286592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0559_range (index : Nat) (lower : 286208 ≤ index) (upper : index < 286720) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 286464 then
    if cut : index < 286336 then
      exact segment_sound _ 286208 128 Update0559_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 286336 128 Update0559_1_checked index (by omega) (by omega)
  else
    if cut : index < 286592 then
      exact segment_sound _ 286464 128 Update0559_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 286592 128 Update0559_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
