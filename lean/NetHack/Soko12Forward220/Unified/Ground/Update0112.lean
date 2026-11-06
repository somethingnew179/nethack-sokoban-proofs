import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0112_0_checked : (List.range' 57344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0112_1_checked : (List.range' 57472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0112_2_checked : (List.range' 57600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0112_3_checked : (List.range' 57728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0112_range (index : Nat) (lower : 57344 ≤ index) (upper : index < 57856) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 57600 then
    if cut : index < 57472 then
      exact segment_sound _ 57344 128 Update0112_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 57472 128 Update0112_1_checked index (by omega) (by omega)
  else
    if cut : index < 57728 then
      exact segment_sound _ 57600 128 Update0112_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 57728 128 Update0112_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
