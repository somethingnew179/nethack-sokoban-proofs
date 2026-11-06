import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0086_0_checked : (List.range' 44032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0086_1_checked : (List.range' 44160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0086_2_checked : (List.range' 44288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0086_3_checked : (List.range' 44416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0086_range (index : Nat) (lower : 44032 ≤ index) (upper : index < 44544) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 44288 then
    if cut : index < 44160 then
      exact segment_sound _ 44032 128 Update0086_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 44160 128 Update0086_1_checked index (by omega) (by omega)
  else
    if cut : index < 44416 then
      exact segment_sound _ 44288 128 Update0086_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 44416 128 Update0086_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
