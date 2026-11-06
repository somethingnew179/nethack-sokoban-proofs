import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0031_0_checked : (List.range' 15872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0031_1_checked : (List.range' 16000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0031_2_checked : (List.range' 16128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0031_3_checked : (List.range' 16256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0031_range (index : Nat) (lower : 15872 ≤ index) (upper : index < 16384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 16128 then
    if cut : index < 16000 then
      exact segment_sound _ 15872 128 Update0031_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16000 128 Update0031_1_checked index (by omega) (by omega)
  else
    if cut : index < 16256 then
      exact segment_sound _ 16128 128 Update0031_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 16256 128 Update0031_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
