import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0229_0_checked : (List.range' 117248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0229_1_checked : (List.range' 117376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0229_2_checked : (List.range' 117504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0229_3_checked : (List.range' 117632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0229_range (index : Nat) (lower : 117248 ≤ index) (upper : index < 117760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 117504 then
    if cut : index < 117376 then
      exact segment_sound _ 117248 128 Update0229_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 117376 128 Update0229_1_checked index (by omega) (by omega)
  else
    if cut : index < 117632 then
      exact segment_sound _ 117504 128 Update0229_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 117632 128 Update0229_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
