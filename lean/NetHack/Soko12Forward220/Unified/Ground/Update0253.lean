import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0253_0_checked : (List.range' 129536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0253_1_checked : (List.range' 129664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0253_2_checked : (List.range' 129792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0253_3_checked : (List.range' 129920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0253_range (index : Nat) (lower : 129536 ≤ index) (upper : index < 130048) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 129792 then
    if cut : index < 129664 then
      exact segment_sound _ 129536 128 Update0253_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 129664 128 Update0253_1_checked index (by omega) (by omega)
  else
    if cut : index < 129920 then
      exact segment_sound _ 129792 128 Update0253_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 129920 128 Update0253_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
