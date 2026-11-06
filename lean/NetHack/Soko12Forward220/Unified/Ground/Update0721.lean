import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0721_0_checked : (List.range' 369152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0721_1_checked : (List.range' 369280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0721_2_checked : (List.range' 369408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0721_3_checked : (List.range' 369536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0721_range (index : Nat) (lower : 369152 ≤ index) (upper : index < 369664) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 369408 then
    if cut : index < 369280 then
      exact segment_sound _ 369152 128 Update0721_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 369280 128 Update0721_1_checked index (by omega) (by omega)
  else
    if cut : index < 369536 then
      exact segment_sound _ 369408 128 Update0721_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 369536 128 Update0721_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
