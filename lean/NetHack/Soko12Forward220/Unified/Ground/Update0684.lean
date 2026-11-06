import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0684_0_checked : (List.range' 350208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0684_1_checked : (List.range' 350336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0684_2_checked : (List.range' 350464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0684_3_checked : (List.range' 350592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0684_range (index : Nat) (lower : 350208 ≤ index) (upper : index < 350720) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 350464 then
    if cut : index < 350336 then
      exact segment_sound _ 350208 128 Update0684_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 350336 128 Update0684_1_checked index (by omega) (by omega)
  else
    if cut : index < 350592 then
      exact segment_sound _ 350464 128 Update0684_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 350592 128 Update0684_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
