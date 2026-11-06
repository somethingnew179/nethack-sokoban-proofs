import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0408_0_checked : (List.range' 208896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0408_1_checked : (List.range' 209024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0408_2_checked : (List.range' 209152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0408_3_checked : (List.range' 209280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0408_range (index : Nat) (lower : 208896 ≤ index) (upper : index < 209408) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 209152 then
    if cut : index < 209024 then
      exact segment_sound _ 208896 128 Update0408_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209024 128 Update0408_1_checked index (by omega) (by omega)
  else
    if cut : index < 209280 then
      exact segment_sound _ 209152 128 Update0408_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209280 128 Update0408_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
