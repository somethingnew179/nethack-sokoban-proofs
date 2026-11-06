import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0551_0_checked : (List.range' 282112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0551_1_checked : (List.range' 282240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0551_2_checked : (List.range' 282368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0551_3_checked : (List.range' 282496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0551_range (index : Nat) (lower : 282112 ≤ index) (upper : index < 282624) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 282368 then
    if cut : index < 282240 then
      exact segment_sound _ 282112 128 Update0551_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 282240 128 Update0551_1_checked index (by omega) (by omega)
  else
    if cut : index < 282496 then
      exact segment_sound _ 282368 128 Update0551_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 282496 128 Update0551_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
