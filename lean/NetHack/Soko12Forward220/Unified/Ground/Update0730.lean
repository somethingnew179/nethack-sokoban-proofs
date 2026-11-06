import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0730_0_checked : (List.range' 373760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0730_1_checked : (List.range' 373888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0730_2_checked : (List.range' 374016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0730_3_checked : (List.range' 374144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0730_range (index : Nat) (lower : 373760 ≤ index) (upper : index < 374272) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 374016 then
    if cut : index < 373888 then
      exact segment_sound _ 373760 128 Update0730_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 373888 128 Update0730_1_checked index (by omega) (by omega)
  else
    if cut : index < 374144 then
      exact segment_sound _ 374016 128 Update0730_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 374144 128 Update0730_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
