import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0162_0_checked : (List.range' 82944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0162_1_checked : (List.range' 83072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0162_2_checked : (List.range' 83200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0162_3_checked : (List.range' 83328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0162_range (index : Nat) (lower : 82944 ≤ index) (upper : index < 83456) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 83200 then
    if cut : index < 83072 then
      exact segment_sound _ 82944 128 Update0162_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 83072 128 Update0162_1_checked index (by omega) (by omega)
  else
    if cut : index < 83328 then
      exact segment_sound _ 83200 128 Update0162_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 83328 128 Update0162_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
