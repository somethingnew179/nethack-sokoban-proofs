import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0576_0_checked : (List.range' 294912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0576_1_checked : (List.range' 295040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0576_2_checked : (List.range' 295168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0576_3_checked : (List.range' 295296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0576_range (index : Nat) (lower : 294912 ≤ index) (upper : index < 295424) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 295168 then
    if cut : index < 295040 then
      exact segment_sound _ 294912 128 Update0576_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 295040 128 Update0576_1_checked index (by omega) (by omega)
  else
    if cut : index < 295296 then
      exact segment_sound _ 295168 128 Update0576_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 295296 128 Update0576_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
