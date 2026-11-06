import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0339_0_checked : (List.range' 173568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0339_1_checked : (List.range' 173696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0339_2_checked : (List.range' 173824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0339_3_checked : (List.range' 173952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0339_range (index : Nat) (lower : 173568 ≤ index) (upper : index < 174080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 173824 then
    if cut : index < 173696 then
      exact segment_sound _ 173568 128 Update0339_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 173696 128 Update0339_1_checked index (by omega) (by omega)
  else
    if cut : index < 173952 then
      exact segment_sound _ 173824 128 Update0339_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 173952 128 Update0339_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
