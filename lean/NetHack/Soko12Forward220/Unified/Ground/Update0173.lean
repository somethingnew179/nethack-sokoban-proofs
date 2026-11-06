import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0173_0_checked : (List.range' 88576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0173_1_checked : (List.range' 88704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0173_2_checked : (List.range' 88832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0173_3_checked : (List.range' 88960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0173_range (index : Nat) (lower : 88576 ≤ index) (upper : index < 89088) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 88832 then
    if cut : index < 88704 then
      exact segment_sound _ 88576 128 Update0173_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 88704 128 Update0173_1_checked index (by omega) (by omega)
  else
    if cut : index < 88960 then
      exact segment_sound _ 88832 128 Update0173_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 88960 128 Update0173_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
