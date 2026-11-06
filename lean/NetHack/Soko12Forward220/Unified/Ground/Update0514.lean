import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0514_0_checked : (List.range' 263168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0514_1_checked : (List.range' 263296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0514_2_checked : (List.range' 263424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0514_3_checked : (List.range' 263552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0514_range (index : Nat) (lower : 263168 ≤ index) (upper : index < 263680) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 263424 then
    if cut : index < 263296 then
      exact segment_sound _ 263168 128 Update0514_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 263296 128 Update0514_1_checked index (by omega) (by omega)
  else
    if cut : index < 263552 then
      exact segment_sound _ 263424 128 Update0514_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 263552 128 Update0514_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
