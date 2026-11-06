import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0446_0_checked : (List.range' 228352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0446_1_checked : (List.range' 228480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0446_2_checked : (List.range' 228608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0446_3_checked : (List.range' 228736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0446_range (index : Nat) (lower : 228352 ≤ index) (upper : index < 228864) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 228608 then
    if cut : index < 228480 then
      exact segment_sound _ 228352 128 Update0446_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 228480 128 Update0446_1_checked index (by omega) (by omega)
  else
    if cut : index < 228736 then
      exact segment_sound _ 228608 128 Update0446_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 228736 128 Update0446_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
