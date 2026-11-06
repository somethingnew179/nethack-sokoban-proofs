import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0065_0_checked : (List.range' 33280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0065_1_checked : (List.range' 33408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0065_2_checked : (List.range' 33536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0065_3_checked : (List.range' 33664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0065_range (index : Nat) (lower : 33280 ≤ index) (upper : index < 33792) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 33536 then
    if cut : index < 33408 then
      exact segment_sound _ 33280 128 Update0065_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 33408 128 Update0065_1_checked index (by omega) (by omega)
  else
    if cut : index < 33664 then
      exact segment_sound _ 33536 128 Update0065_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 33664 128 Update0065_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
