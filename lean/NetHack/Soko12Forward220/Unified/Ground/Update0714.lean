import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0714_0_checked : (List.range' 365568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0714_1_checked : (List.range' 365696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0714_2_checked : (List.range' 365824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0714_3_checked : (List.range' 365952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0714_range (index : Nat) (lower : 365568 ≤ index) (upper : index < 366080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 365824 then
    if cut : index < 365696 then
      exact segment_sound _ 365568 128 Update0714_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365696 128 Update0714_1_checked index (by omega) (by omega)
  else
    if cut : index < 365952 then
      exact segment_sound _ 365824 128 Update0714_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365952 128 Update0714_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
