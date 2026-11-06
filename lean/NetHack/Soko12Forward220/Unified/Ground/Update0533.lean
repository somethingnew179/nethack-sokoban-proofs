import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0533_0_checked : (List.range' 272896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0533_1_checked : (List.range' 273024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0533_2_checked : (List.range' 273152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0533_3_checked : (List.range' 273280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0533_range (index : Nat) (lower : 272896 ≤ index) (upper : index < 273408) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 273152 then
    if cut : index < 273024 then
      exact segment_sound _ 272896 128 Update0533_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 273024 128 Update0533_1_checked index (by omega) (by omega)
  else
    if cut : index < 273280 then
      exact segment_sound _ 273152 128 Update0533_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 273280 128 Update0533_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
