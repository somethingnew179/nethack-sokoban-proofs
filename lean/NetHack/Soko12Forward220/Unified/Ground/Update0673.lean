import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0673_0_checked : (List.range' 344576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0673_1_checked : (List.range' 344704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0673_2_checked : (List.range' 344832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0673_3_checked : (List.range' 344960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0673_range (index : Nat) (lower : 344576 ≤ index) (upper : index < 345088) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 344832 then
    if cut : index < 344704 then
      exact segment_sound _ 344576 128 Update0673_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 344704 128 Update0673_1_checked index (by omega) (by omega)
  else
    if cut : index < 344960 then
      exact segment_sound _ 344832 128 Update0673_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 344960 128 Update0673_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
