import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0405_0_checked : (List.range' 207360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0405_1_checked : (List.range' 207488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0405_2_checked : (List.range' 207616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0405_3_checked : (List.range' 207744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0405_range (index : Nat) (lower : 207360 ≤ index) (upper : index < 207872) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 207616 then
    if cut : index < 207488 then
      exact segment_sound _ 207360 128 Update0405_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 207488 128 Update0405_1_checked index (by omega) (by omega)
  else
    if cut : index < 207744 then
      exact segment_sound _ 207616 128 Update0405_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 207744 128 Update0405_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
