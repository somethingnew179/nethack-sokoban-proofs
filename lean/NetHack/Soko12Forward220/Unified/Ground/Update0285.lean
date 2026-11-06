import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0285_0_checked : (List.range' 145920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0285_1_checked : (List.range' 146048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0285_2_checked : (List.range' 146176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0285_3_checked : (List.range' 146304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0285_range (index : Nat) (lower : 145920 ≤ index) (upper : index < 146432) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 146176 then
    if cut : index < 146048 then
      exact segment_sound _ 145920 128 Update0285_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 146048 128 Update0285_1_checked index (by omega) (by omega)
  else
    if cut : index < 146304 then
      exact segment_sound _ 146176 128 Update0285_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 146304 128 Update0285_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
