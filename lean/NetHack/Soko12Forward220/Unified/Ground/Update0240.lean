import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0240_0_checked : (List.range' 122880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0240_1_checked : (List.range' 123008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0240_2_checked : (List.range' 123136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0240_3_checked : (List.range' 123264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0240_range (index : Nat) (lower : 122880 ≤ index) (upper : index < 123392) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 123136 then
    if cut : index < 123008 then
      exact segment_sound _ 122880 128 Update0240_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 123008 128 Update0240_1_checked index (by omega) (by omega)
  else
    if cut : index < 123264 then
      exact segment_sound _ 123136 128 Update0240_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 123264 128 Update0240_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
