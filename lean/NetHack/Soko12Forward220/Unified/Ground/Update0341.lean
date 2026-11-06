import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0341_0_checked : (List.range' 174592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0341_1_checked : (List.range' 174720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0341_2_checked : (List.range' 174848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0341_3_checked : (List.range' 174976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0341_range (index : Nat) (lower : 174592 ≤ index) (upper : index < 175104) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 174848 then
    if cut : index < 174720 then
      exact segment_sound _ 174592 128 Update0341_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 174720 128 Update0341_1_checked index (by omega) (by omega)
  else
    if cut : index < 174976 then
      exact segment_sound _ 174848 128 Update0341_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 174976 128 Update0341_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
