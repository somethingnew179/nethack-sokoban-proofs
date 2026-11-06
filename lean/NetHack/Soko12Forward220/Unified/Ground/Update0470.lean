import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0470_0_checked : (List.range' 240640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0470_1_checked : (List.range' 240768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0470_2_checked : (List.range' 240896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0470_3_checked : (List.range' 241024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0470_range (index : Nat) (lower : 240640 ≤ index) (upper : index < 241152) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 240896 then
    if cut : index < 240768 then
      exact segment_sound _ 240640 128 Update0470_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 240768 128 Update0470_1_checked index (by omega) (by omega)
  else
    if cut : index < 241024 then
      exact segment_sound _ 240896 128 Update0470_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 241024 128 Update0470_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
