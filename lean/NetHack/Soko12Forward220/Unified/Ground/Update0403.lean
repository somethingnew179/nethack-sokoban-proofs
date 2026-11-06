import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0403_0_checked : (List.range' 206336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0403_1_checked : (List.range' 206464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0403_2_checked : (List.range' 206592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0403_3_checked : (List.range' 206720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0403_range (index : Nat) (lower : 206336 ≤ index) (upper : index < 206848) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 206592 then
    if cut : index < 206464 then
      exact segment_sound _ 206336 128 Update0403_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 206464 128 Update0403_1_checked index (by omega) (by omega)
  else
    if cut : index < 206720 then
      exact segment_sound _ 206592 128 Update0403_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 206720 128 Update0403_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
