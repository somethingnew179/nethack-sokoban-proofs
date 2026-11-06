import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0618_0_checked : (List.range' 316416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0618_1_checked : (List.range' 316544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0618_2_checked : (List.range' 316672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0618_3_checked : (List.range' 316800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0618_range (index : Nat) (lower : 316416 ≤ index) (upper : index < 316928) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 316672 then
    if cut : index < 316544 then
      exact segment_sound _ 316416 128 Update0618_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 316544 128 Update0618_1_checked index (by omega) (by omega)
  else
    if cut : index < 316800 then
      exact segment_sound _ 316672 128 Update0618_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 316800 128 Update0618_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
