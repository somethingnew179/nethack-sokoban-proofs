import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0414_0_checked : (List.range' 211968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0414_1_checked : (List.range' 212096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0414_2_checked : (List.range' 212224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0414_3_checked : (List.range' 212352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0414_range (index : Nat) (lower : 211968 ≤ index) (upper : index < 212480) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 212224 then
    if cut : index < 212096 then
      exact segment_sound _ 211968 128 Update0414_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 212096 128 Update0414_1_checked index (by omega) (by omega)
  else
    if cut : index < 212352 then
      exact segment_sound _ 212224 128 Update0414_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 212352 128 Update0414_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
