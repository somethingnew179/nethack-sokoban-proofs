import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0528_0_checked : (List.range' 270336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0528_1_checked : (List.range' 270464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0528_2_checked : (List.range' 270592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0528_3_checked : (List.range' 270720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0528_range (index : Nat) (lower : 270336 ≤ index) (upper : index < 270848) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 270592 then
    if cut : index < 270464 then
      exact segment_sound _ 270336 128 Update0528_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270464 128 Update0528_1_checked index (by omega) (by omega)
  else
    if cut : index < 270720 then
      exact segment_sound _ 270592 128 Update0528_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270720 128 Update0528_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
