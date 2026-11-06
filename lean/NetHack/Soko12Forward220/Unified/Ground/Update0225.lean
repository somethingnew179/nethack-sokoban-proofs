import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0225_0_checked : (List.range' 115200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0225_1_checked : (List.range' 115328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0225_2_checked : (List.range' 115456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0225_3_checked : (List.range' 115584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0225_range (index : Nat) (lower : 115200 ≤ index) (upper : index < 115712) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 115456 then
    if cut : index < 115328 then
      exact segment_sound _ 115200 128 Update0225_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 115328 128 Update0225_1_checked index (by omega) (by omega)
  else
    if cut : index < 115584 then
      exact segment_sound _ 115456 128 Update0225_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 115584 128 Update0225_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
