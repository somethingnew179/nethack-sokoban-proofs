import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0244_0_checked : (List.range' 124928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0244_1_checked : (List.range' 125056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0244_2_checked : (List.range' 125184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0244_3_checked : (List.range' 125312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0244_range (index : Nat) (lower : 124928 ≤ index) (upper : index < 125440) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 125184 then
    if cut : index < 125056 then
      exact segment_sound _ 124928 128 Update0244_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 125056 128 Update0244_1_checked index (by omega) (by omega)
  else
    if cut : index < 125312 then
      exact segment_sound _ 125184 128 Update0244_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 125312 128 Update0244_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
