import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0569_0_checked : (List.range' 291328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0569_1_checked : (List.range' 291456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0569_2_checked : (List.range' 291584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0569_3_checked : (List.range' 291712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0569_range (index : Nat) (lower : 291328 ≤ index) (upper : index < 291840) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 291584 then
    if cut : index < 291456 then
      exact segment_sound _ 291328 128 Update0569_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291456 128 Update0569_1_checked index (by omega) (by omega)
  else
    if cut : index < 291712 then
      exact segment_sound _ 291584 128 Update0569_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291712 128 Update0569_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
