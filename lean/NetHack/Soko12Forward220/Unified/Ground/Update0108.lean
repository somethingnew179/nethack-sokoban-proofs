import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0108_0_checked : (List.range' 55296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0108_1_checked : (List.range' 55424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0108_2_checked : (List.range' 55552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0108_3_checked : (List.range' 55680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0108_range (index : Nat) (lower : 55296 ≤ index) (upper : index < 55808) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 55552 then
    if cut : index < 55424 then
      exact segment_sound _ 55296 128 Update0108_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 55424 128 Update0108_1_checked index (by omega) (by omega)
  else
    if cut : index < 55680 then
      exact segment_sound _ 55552 128 Update0108_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 55680 128 Update0108_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
