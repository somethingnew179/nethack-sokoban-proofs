import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0505_0_checked : (List.range' 258560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0505_1_checked : (List.range' 258688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0505_2_checked : (List.range' 258816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0505_3_checked : (List.range' 258944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0505_range (index : Nat) (lower : 258560 ≤ index) (upper : index < 259072) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 258816 then
    if cut : index < 258688 then
      exact segment_sound _ 258560 128 Update0505_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 258688 128 Update0505_1_checked index (by omega) (by omega)
  else
    if cut : index < 258944 then
      exact segment_sound _ 258816 128 Update0505_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 258944 128 Update0505_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
