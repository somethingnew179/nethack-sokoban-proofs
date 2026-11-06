import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0520_0_checked : (List.range' 266240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0520_1_checked : (List.range' 266368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0520_2_checked : (List.range' 266496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0520_3_checked : (List.range' 266624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0520_range (index : Nat) (lower : 266240 ≤ index) (upper : index < 266752) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 266496 then
    if cut : index < 266368 then
      exact segment_sound _ 266240 128 Update0520_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266368 128 Update0520_1_checked index (by omega) (by omega)
  else
    if cut : index < 266624 then
      exact segment_sound _ 266496 128 Update0520_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266624 128 Update0520_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
