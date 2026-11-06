import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0194_0_checked : (List.range' 99328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0194_1_checked : (List.range' 99456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0194_2_checked : (List.range' 99584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0194_3_checked : (List.range' 99712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0194_range (index : Nat) (lower : 99328 ≤ index) (upper : index < 99840) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 99584 then
    if cut : index < 99456 then
      exact segment_sound _ 99328 128 Update0194_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 99456 128 Update0194_1_checked index (by omega) (by omega)
  else
    if cut : index < 99712 then
      exact segment_sound _ 99584 128 Update0194_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 99712 128 Update0194_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
