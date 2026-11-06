import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0633_0_checked : (List.range' 324096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0633_1_checked : (List.range' 324224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0633_2_checked : (List.range' 324352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0633_3_checked : (List.range' 324480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0633_range (index : Nat) (lower : 324096 ≤ index) (upper : index < 324608) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 324352 then
    if cut : index < 324224 then
      exact segment_sound _ 324096 128 Update0633_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324224 128 Update0633_1_checked index (by omega) (by omega)
  else
    if cut : index < 324480 then
      exact segment_sound _ 324352 128 Update0633_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324480 128 Update0633_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
