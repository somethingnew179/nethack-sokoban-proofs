import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0572_0_checked : (List.range' 292864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0572_1_checked : (List.range' 292992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0572_2_checked : (List.range' 293120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0572_3_checked : (List.range' 293248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0572_range (index : Nat) (lower : 292864 ≤ index) (upper : index < 293376) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 293120 then
    if cut : index < 292992 then
      exact segment_sound _ 292864 128 Update0572_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292992 128 Update0572_1_checked index (by omega) (by omega)
  else
    if cut : index < 293248 then
      exact segment_sound _ 293120 128 Update0572_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293248 128 Update0572_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
