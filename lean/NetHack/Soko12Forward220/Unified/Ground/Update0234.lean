import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0234_0_checked : (List.range' 119808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0234_1_checked : (List.range' 119936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0234_2_checked : (List.range' 120064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0234_3_checked : (List.range' 120192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0234_range (index : Nat) (lower : 119808 ≤ index) (upper : index < 120320) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 120064 then
    if cut : index < 119936 then
      exact segment_sound _ 119808 128 Update0234_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 119936 128 Update0234_1_checked index (by omega) (by omega)
  else
    if cut : index < 120192 then
      exact segment_sound _ 120064 128 Update0234_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 120192 128 Update0234_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
