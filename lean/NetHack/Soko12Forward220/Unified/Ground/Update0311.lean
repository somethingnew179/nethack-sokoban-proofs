import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0311_0_checked : (List.range' 159232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0311_1_checked : (List.range' 159360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0311_2_checked : (List.range' 159488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0311_3_checked : (List.range' 159616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0311_range (index : Nat) (lower : 159232 ≤ index) (upper : index < 159744) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 159488 then
    if cut : index < 159360 then
      exact segment_sound _ 159232 128 Update0311_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159360 128 Update0311_1_checked index (by omega) (by omega)
  else
    if cut : index < 159616 then
      exact segment_sound _ 159488 128 Update0311_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 159616 128 Update0311_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
