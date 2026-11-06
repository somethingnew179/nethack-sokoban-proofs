import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0647_0_checked : (List.range' 331264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0647_1_checked : (List.range' 331392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0647_2_checked : (List.range' 331520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0647_3_checked : (List.range' 331648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0647_range (index : Nat) (lower : 331264 ≤ index) (upper : index < 331776) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 331520 then
    if cut : index < 331392 then
      exact segment_sound _ 331264 128 Update0647_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 331392 128 Update0647_1_checked index (by omega) (by omega)
  else
    if cut : index < 331648 then
      exact segment_sound _ 331520 128 Update0647_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 331648 128 Update0647_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
