import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0147_0_checked : (List.range' 75264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0147_1_checked : (List.range' 75392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0147_2_checked : (List.range' 75520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0147_3_checked : (List.range' 75648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0147_range (index : Nat) (lower : 75264 ≤ index) (upper : index < 75776) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 75520 then
    if cut : index < 75392 then
      exact segment_sound _ 75264 128 Update0147_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 75392 128 Update0147_1_checked index (by omega) (by omega)
  else
    if cut : index < 75648 then
      exact segment_sound _ 75520 128 Update0147_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 75648 128 Update0147_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
