import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0539_0_checked : (List.range' 275968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0539_1_checked : (List.range' 276096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0539_2_checked : (List.range' 276224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0539_3_checked : (List.range' 276352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0539_range (index : Nat) (lower : 275968 ≤ index) (upper : index < 276480) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 276224 then
    if cut : index < 276096 then
      exact segment_sound _ 275968 128 Update0539_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 276096 128 Update0539_1_checked index (by omega) (by omega)
  else
    if cut : index < 276352 then
      exact segment_sound _ 276224 128 Update0539_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 276352 128 Update0539_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
