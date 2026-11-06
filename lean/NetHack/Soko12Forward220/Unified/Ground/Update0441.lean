import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0441_0_checked : (List.range' 225792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0441_1_checked : (List.range' 225920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0441_2_checked : (List.range' 226048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0441_3_checked : (List.range' 226176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0441_range (index : Nat) (lower : 225792 ≤ index) (upper : index < 226304) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 226048 then
    if cut : index < 225920 then
      exact segment_sound _ 225792 128 Update0441_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 225920 128 Update0441_1_checked index (by omega) (by omega)
  else
    if cut : index < 226176 then
      exact segment_sound _ 226048 128 Update0441_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 226176 128 Update0441_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
