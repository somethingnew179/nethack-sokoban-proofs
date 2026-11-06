import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0346_0_checked : (List.range' 177152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0346_1_checked : (List.range' 177280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0346_2_checked : (List.range' 177408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0346_3_checked : (List.range' 177536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0346_range (index : Nat) (lower : 177152 ≤ index) (upper : index < 177664) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 177408 then
    if cut : index < 177280 then
      exact segment_sound _ 177152 128 Update0346_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 177280 128 Update0346_1_checked index (by omega) (by omega)
  else
    if cut : index < 177536 then
      exact segment_sound _ 177408 128 Update0346_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 177536 128 Update0346_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
