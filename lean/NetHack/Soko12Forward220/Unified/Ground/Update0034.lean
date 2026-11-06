import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0034_0_checked : (List.range' 17408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0034_1_checked : (List.range' 17536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0034_2_checked : (List.range' 17664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0034_3_checked : (List.range' 17792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0034_range (index : Nat) (lower : 17408 ≤ index) (upper : index < 17920) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 17664 then
    if cut : index < 17536 then
      exact segment_sound _ 17408 128 Update0034_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 17536 128 Update0034_1_checked index (by omega) (by omega)
  else
    if cut : index < 17792 then
      exact segment_sound _ 17664 128 Update0034_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 17792 128 Update0034_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
