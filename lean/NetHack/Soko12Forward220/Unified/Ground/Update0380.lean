import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0380_0_checked : (List.range' 194560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0380_1_checked : (List.range' 194688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0380_2_checked : (List.range' 194816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0380_3_checked : (List.range' 194944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0380_range (index : Nat) (lower : 194560 ≤ index) (upper : index < 195072) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 194816 then
    if cut : index < 194688 then
      exact segment_sound _ 194560 128 Update0380_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 194688 128 Update0380_1_checked index (by omega) (by omega)
  else
    if cut : index < 194944 then
      exact segment_sound _ 194816 128 Update0380_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 194944 128 Update0380_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
