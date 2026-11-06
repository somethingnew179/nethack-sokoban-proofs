import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0160_0_checked : (List.range' 81920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0160_1_checked : (List.range' 82048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0160_2_checked : (List.range' 82176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0160_3_checked : (List.range' 82304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0160_range (index : Nat) (lower : 81920 ≤ index) (upper : index < 82432) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 82176 then
    if cut : index < 82048 then
      exact segment_sound _ 81920 128 Update0160_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 82048 128 Update0160_1_checked index (by omega) (by omega)
  else
    if cut : index < 82304 then
      exact segment_sound _ 82176 128 Update0160_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 82304 128 Update0160_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
