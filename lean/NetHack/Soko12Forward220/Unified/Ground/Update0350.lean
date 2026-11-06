import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0350_0_checked : (List.range' 179200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0350_1_checked : (List.range' 179328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0350_2_checked : (List.range' 179456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0350_3_checked : (List.range' 179584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0350_range (index : Nat) (lower : 179200 ≤ index) (upper : index < 179712) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 179456 then
    if cut : index < 179328 then
      exact segment_sound _ 179200 128 Update0350_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 179328 128 Update0350_1_checked index (by omega) (by omega)
  else
    if cut : index < 179584 then
      exact segment_sound _ 179456 128 Update0350_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 179584 128 Update0350_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
