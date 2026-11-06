import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0075_0_checked : (List.range' 38400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0075_1_checked : (List.range' 38528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0075_2_checked : (List.range' 38656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0075_3_checked : (List.range' 38784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0075_range (index : Nat) (lower : 38400 ≤ index) (upper : index < 38912) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 38656 then
    if cut : index < 38528 then
      exact segment_sound _ 38400 128 Update0075_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38528 128 Update0075_1_checked index (by omega) (by omega)
  else
    if cut : index < 38784 then
      exact segment_sound _ 38656 128 Update0075_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38784 128 Update0075_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
