import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0094_0_checked : (List.range' 48128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0094_1_checked : (List.range' 48256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0094_2_checked : (List.range' 48384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0094_3_checked : (List.range' 48512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0094_range (index : Nat) (lower : 48128 ≤ index) (upper : index < 48640) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 48384 then
    if cut : index < 48256 then
      exact segment_sound _ 48128 128 Update0094_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 48256 128 Update0094_1_checked index (by omega) (by omega)
  else
    if cut : index < 48512 then
      exact segment_sound _ 48384 128 Update0094_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 48512 128 Update0094_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
