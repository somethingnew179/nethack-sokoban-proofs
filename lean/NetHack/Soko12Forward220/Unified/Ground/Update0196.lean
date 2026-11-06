import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0196_0_checked : (List.range' 100352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0196_1_checked : (List.range' 100480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0196_2_checked : (List.range' 100608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0196_3_checked : (List.range' 100736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0196_range (index : Nat) (lower : 100352 ≤ index) (upper : index < 100864) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 100608 then
    if cut : index < 100480 then
      exact segment_sound _ 100352 128 Update0196_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 100480 128 Update0196_1_checked index (by omega) (by omega)
  else
    if cut : index < 100736 then
      exact segment_sound _ 100608 128 Update0196_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 100736 128 Update0196_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
