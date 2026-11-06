import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0447_0_checked : (List.range' 228864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0447_1_checked : (List.range' 228992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0447_2_checked : (List.range' 229120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0447_3_checked : (List.range' 229248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0447_range (index : Nat) (lower : 228864 ≤ index) (upper : index < 229376) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 229120 then
    if cut : index < 228992 then
      exact segment_sound _ 228864 128 Update0447_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 228992 128 Update0447_1_checked index (by omega) (by omega)
  else
    if cut : index < 229248 then
      exact segment_sound _ 229120 128 Update0447_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 229248 128 Update0447_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
