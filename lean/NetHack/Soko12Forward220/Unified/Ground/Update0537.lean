import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0537_0_checked : (List.range' 274944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0537_1_checked : (List.range' 275072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0537_2_checked : (List.range' 275200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0537_3_checked : (List.range' 275328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0537_range (index : Nat) (lower : 274944 ≤ index) (upper : index < 275456) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 275200 then
    if cut : index < 275072 then
      exact segment_sound _ 274944 128 Update0537_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275072 128 Update0537_1_checked index (by omega) (by omega)
  else
    if cut : index < 275328 then
      exact segment_sound _ 275200 128 Update0537_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275328 128 Update0537_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
