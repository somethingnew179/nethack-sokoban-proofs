import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0370_0_checked : (List.range' 189440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0370_1_checked : (List.range' 189568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0370_2_checked : (List.range' 189696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0370_3_checked : (List.range' 189824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0370_range (index : Nat) (lower : 189440 ≤ index) (upper : index < 189952) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 189696 then
    if cut : index < 189568 then
      exact segment_sound _ 189440 128 Update0370_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 189568 128 Update0370_1_checked index (by omega) (by omega)
  else
    if cut : index < 189824 then
      exact segment_sound _ 189696 128 Update0370_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 189824 128 Update0370_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
