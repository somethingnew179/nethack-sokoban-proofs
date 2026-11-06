import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0163_0_checked : (List.range' 83456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0163_1_checked : (List.range' 83584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0163_2_checked : (List.range' 83712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0163_3_checked : (List.range' 83840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0163_range (index : Nat) (lower : 83456 ≤ index) (upper : index < 83968) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 83712 then
    if cut : index < 83584 then
      exact segment_sound _ 83456 128 Update0163_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 83584 128 Update0163_1_checked index (by omega) (by omega)
  else
    if cut : index < 83840 then
      exact segment_sound _ 83712 128 Update0163_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 83840 128 Update0163_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
