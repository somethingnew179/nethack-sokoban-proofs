import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0566_0_checked : (List.range' 289792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0566_1_checked : (List.range' 289920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0566_2_checked : (List.range' 290048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0566_3_checked : (List.range' 290176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0566_range (index : Nat) (lower : 289792 ≤ index) (upper : index < 290304) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 290048 then
    if cut : index < 289920 then
      exact segment_sound _ 289792 128 Update0566_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 289920 128 Update0566_1_checked index (by omega) (by omega)
  else
    if cut : index < 290176 then
      exact segment_sound _ 290048 128 Update0566_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 290176 128 Update0566_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
