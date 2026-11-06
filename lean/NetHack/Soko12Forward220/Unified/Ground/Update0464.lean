import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0464_0_checked : (List.range' 237568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0464_1_checked : (List.range' 237696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0464_2_checked : (List.range' 237824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0464_3_checked : (List.range' 237952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0464_range (index : Nat) (lower : 237568 ≤ index) (upper : index < 238080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 237824 then
    if cut : index < 237696 then
      exact segment_sound _ 237568 128 Update0464_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 237696 128 Update0464_1_checked index (by omega) (by omega)
  else
    if cut : index < 237952 then
      exact segment_sound _ 237824 128 Update0464_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 237952 128 Update0464_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
