import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0258_0_checked : (List.range' 132096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0258_1_checked : (List.range' 132224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0258_2_checked : (List.range' 132352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0258_3_checked : (List.range' 132480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0258_range (index : Nat) (lower : 132096 ≤ index) (upper : index < 132608) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 132352 then
    if cut : index < 132224 then
      exact segment_sound _ 132096 128 Update0258_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 132224 128 Update0258_1_checked index (by omega) (by omega)
  else
    if cut : index < 132480 then
      exact segment_sound _ 132352 128 Update0258_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 132480 128 Update0258_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
