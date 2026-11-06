import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0073_0_checked : (List.range' 37376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0073_1_checked : (List.range' 37504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0073_2_checked : (List.range' 37632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0073_3_checked : (List.range' 37760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0073_range (index : Nat) (lower : 37376 ≤ index) (upper : index < 37888) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 37632 then
    if cut : index < 37504 then
      exact segment_sound _ 37376 128 Update0073_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 37504 128 Update0073_1_checked index (by omega) (by omega)
  else
    if cut : index < 37760 then
      exact segment_sound _ 37632 128 Update0073_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 37760 128 Update0073_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
