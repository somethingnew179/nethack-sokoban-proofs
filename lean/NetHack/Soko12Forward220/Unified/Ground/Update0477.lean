import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0477_0_checked : (List.range' 244224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0477_1_checked : (List.range' 244352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0477_2_checked : (List.range' 244480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0477_3_checked : (List.range' 244608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0477_range (index : Nat) (lower : 244224 ≤ index) (upper : index < 244736) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 244480 then
    if cut : index < 244352 then
      exact segment_sound _ 244224 128 Update0477_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244352 128 Update0477_1_checked index (by omega) (by omega)
  else
    if cut : index < 244608 then
      exact segment_sound _ 244480 128 Update0477_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244608 128 Update0477_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
