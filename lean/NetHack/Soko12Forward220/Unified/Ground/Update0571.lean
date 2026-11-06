import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0571_0_checked : (List.range' 292352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0571_1_checked : (List.range' 292480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0571_2_checked : (List.range' 292608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0571_3_checked : (List.range' 292736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0571_range (index : Nat) (lower : 292352 ≤ index) (upper : index < 292864) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 292608 then
    if cut : index < 292480 then
      exact segment_sound _ 292352 128 Update0571_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292480 128 Update0571_1_checked index (by omega) (by omega)
  else
    if cut : index < 292736 then
      exact segment_sound _ 292608 128 Update0571_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292736 128 Update0571_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
