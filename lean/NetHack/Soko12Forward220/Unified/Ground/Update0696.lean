import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0696_0_checked : (List.range' 356352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0696_1_checked : (List.range' 356480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0696_2_checked : (List.range' 356608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0696_3_checked : (List.range' 356736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0696_range (index : Nat) (lower : 356352 ≤ index) (upper : index < 356864) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 356608 then
    if cut : index < 356480 then
      exact segment_sound _ 356352 128 Update0696_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 356480 128 Update0696_1_checked index (by omega) (by omega)
  else
    if cut : index < 356736 then
      exact segment_sound _ 356608 128 Update0696_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 356736 128 Update0696_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
