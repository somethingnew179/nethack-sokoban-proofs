import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0379_0_checked : (List.range' 194048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0379_1_checked : (List.range' 194176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0379_2_checked : (List.range' 194304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0379_3_checked : (List.range' 194432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0379_range (index : Nat) (lower : 194048 ≤ index) (upper : index < 194560) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 194304 then
    if cut : index < 194176 then
      exact segment_sound _ 194048 128 Update0379_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 194176 128 Update0379_1_checked index (by omega) (by omega)
  else
    if cut : index < 194432 then
      exact segment_sound _ 194304 128 Update0379_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 194432 128 Update0379_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
