import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0398_0_checked : (List.range' 203776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0398_1_checked : (List.range' 203904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0398_2_checked : (List.range' 204032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0398_3_checked : (List.range' 204160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0398_range (index : Nat) (lower : 203776 ≤ index) (upper : index < 204288) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 204032 then
    if cut : index < 203904 then
      exact segment_sound _ 203776 128 Update0398_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 203904 128 Update0398_1_checked index (by omega) (by omega)
  else
    if cut : index < 204160 then
      exact segment_sound _ 204032 128 Update0398_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 204160 128 Update0398_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
