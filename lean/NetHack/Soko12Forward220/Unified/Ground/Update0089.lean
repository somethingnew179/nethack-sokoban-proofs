import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0089_0_checked : (List.range' 45568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0089_1_checked : (List.range' 45696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0089_2_checked : (List.range' 45824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0089_3_checked : (List.range' 45952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0089_range (index : Nat) (lower : 45568 ≤ index) (upper : index < 46080) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 45824 then
    if cut : index < 45696 then
      exact segment_sound _ 45568 128 Update0089_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45696 128 Update0089_1_checked index (by omega) (by omega)
  else
    if cut : index < 45952 then
      exact segment_sound _ 45824 128 Update0089_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45952 128 Update0089_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
