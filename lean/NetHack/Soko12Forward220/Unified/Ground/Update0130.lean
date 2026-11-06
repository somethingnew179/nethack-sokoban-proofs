import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0130_0_checked : (List.range' 66560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0130_1_checked : (List.range' 66688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0130_2_checked : (List.range' 66816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0130_3_checked : (List.range' 66944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0130_range (index : Nat) (lower : 66560 ≤ index) (upper : index < 67072) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 66816 then
    if cut : index < 66688 then
      exact segment_sound _ 66560 128 Update0130_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 66688 128 Update0130_1_checked index (by omega) (by omega)
  else
    if cut : index < 66944 then
      exact segment_sound _ 66816 128 Update0130_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 66944 128 Update0130_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
