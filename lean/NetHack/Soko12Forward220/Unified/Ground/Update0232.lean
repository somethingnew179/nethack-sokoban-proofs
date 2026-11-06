import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0232_0_checked : (List.range' 118784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0232_1_checked : (List.range' 118912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0232_2_checked : (List.range' 119040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0232_3_checked : (List.range' 119168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0232_range (index : Nat) (lower : 118784 ≤ index) (upper : index < 119296) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 119040 then
    if cut : index < 118912 then
      exact segment_sound _ 118784 128 Update0232_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 118912 128 Update0232_1_checked index (by omega) (by omega)
  else
    if cut : index < 119168 then
      exact segment_sound _ 119040 128 Update0232_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 119168 128 Update0232_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
