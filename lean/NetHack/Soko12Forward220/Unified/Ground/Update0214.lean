import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0214_0_checked : (List.range' 109568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0214_1_checked : (List.range' 109696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0214_2_checked : (List.range' 109824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0214_3_checked : (List.range' 109952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0214_range (index : Nat) (lower : 109568 ≤ index) (upper : index < 110080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 109824 then
    if cut : index < 109696 then
      exact segment_sound _ 109568 128 Update0214_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109696 128 Update0214_1_checked index (by omega) (by omega)
  else
    if cut : index < 109952 then
      exact segment_sound _ 109824 128 Update0214_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 109952 128 Update0214_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
