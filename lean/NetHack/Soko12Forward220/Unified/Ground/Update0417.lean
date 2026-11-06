import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0417_0_checked : (List.range' 213504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0417_1_checked : (List.range' 213632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0417_2_checked : (List.range' 213760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0417_3_checked : (List.range' 213888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0417_range (index : Nat) (lower : 213504 ≤ index) (upper : index < 214016) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 213760 then
    if cut : index < 213632 then
      exact segment_sound _ 213504 128 Update0417_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 213632 128 Update0417_1_checked index (by omega) (by omega)
  else
    if cut : index < 213888 then
      exact segment_sound _ 213760 128 Update0417_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 213888 128 Update0417_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
