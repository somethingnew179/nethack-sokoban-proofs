import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0530_0_checked : (List.range' 271360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0530_1_checked : (List.range' 271488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0530_2_checked : (List.range' 271616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0530_3_checked : (List.range' 271744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0530_range (index : Nat) (lower : 271360 ≤ index) (upper : index < 271872) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 271616 then
    if cut : index < 271488 then
      exact segment_sound _ 271360 128 Update0530_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 271488 128 Update0530_1_checked index (by omega) (by omega)
  else
    if cut : index < 271744 then
      exact segment_sound _ 271616 128 Update0530_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 271744 128 Update0530_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
