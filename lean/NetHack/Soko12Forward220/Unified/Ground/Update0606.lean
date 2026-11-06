import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0606_0_checked : (List.range' 310272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0606_1_checked : (List.range' 310400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0606_2_checked : (List.range' 310528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0606_3_checked : (List.range' 310656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0606_range (index : Nat) (lower : 310272 ≤ index) (upper : index < 310784) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 310528 then
    if cut : index < 310400 then
      exact segment_sound _ 310272 128 Update0606_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 310400 128 Update0606_1_checked index (by omega) (by omega)
  else
    if cut : index < 310656 then
      exact segment_sound _ 310528 128 Update0606_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 310656 128 Update0606_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
