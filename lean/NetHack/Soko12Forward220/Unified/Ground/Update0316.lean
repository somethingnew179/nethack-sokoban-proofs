import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0316_0_checked : (List.range' 161792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0316_1_checked : (List.range' 161920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0316_2_checked : (List.range' 162048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0316_3_checked : (List.range' 162176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0316_range (index : Nat) (lower : 161792 ≤ index) (upper : index < 162304) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 162048 then
    if cut : index < 161920 then
      exact segment_sound _ 161792 128 Update0316_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 161920 128 Update0316_1_checked index (by omega) (by omega)
  else
    if cut : index < 162176 then
      exact segment_sound _ 162048 128 Update0316_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 162176 128 Update0316_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
