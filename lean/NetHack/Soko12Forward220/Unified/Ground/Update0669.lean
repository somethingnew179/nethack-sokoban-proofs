import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0669_0_checked : (List.range' 342528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0669_1_checked : (List.range' 342656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0669_2_checked : (List.range' 342784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0669_3_checked : (List.range' 342912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0669_range (index : Nat) (lower : 342528 ≤ index) (upper : index < 343040) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 342784 then
    if cut : index < 342656 then
      exact segment_sound _ 342528 128 Update0669_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342656 128 Update0669_1_checked index (by omega) (by omega)
  else
    if cut : index < 342912 then
      exact segment_sound _ 342784 128 Update0669_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342912 128 Update0669_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
