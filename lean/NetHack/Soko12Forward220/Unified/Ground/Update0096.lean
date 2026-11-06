import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0096_0_checked : (List.range' 49152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0096_1_checked : (List.range' 49280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0096_2_checked : (List.range' 49408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0096_3_checked : (List.range' 49536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0096_range (index : Nat) (lower : 49152 ≤ index) (upper : index < 49664) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 49408 then
    if cut : index < 49280 then
      exact segment_sound _ 49152 128 Update0096_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49280 128 Update0096_1_checked index (by omega) (by omega)
  else
    if cut : index < 49536 then
      exact segment_sound _ 49408 128 Update0096_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49536 128 Update0096_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
