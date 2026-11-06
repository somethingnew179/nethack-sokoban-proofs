import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0026_0_checked : (List.range' 13312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0026_1_checked : (List.range' 13440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0026_2_checked : (List.range' 13568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0026_3_checked : (List.range' 13696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0026_range (index : Nat) (lower : 13312 ≤ index) (upper : index < 13824) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 13568 then
    if cut : index < 13440 then
      exact segment_sound _ 13312 128 Update0026_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 13440 128 Update0026_1_checked index (by omega) (by omega)
  else
    if cut : index < 13696 then
      exact segment_sound _ 13568 128 Update0026_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 13696 128 Update0026_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
