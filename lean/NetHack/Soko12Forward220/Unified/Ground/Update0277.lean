import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0277_0_checked : (List.range' 141824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0277_1_checked : (List.range' 141952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0277_2_checked : (List.range' 142080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0277_3_checked : (List.range' 142208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0277_range (index : Nat) (lower : 141824 ≤ index) (upper : index < 142336) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 142080 then
    if cut : index < 141952 then
      exact segment_sound _ 141824 128 Update0277_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141952 128 Update0277_1_checked index (by omega) (by omega)
  else
    if cut : index < 142208 then
      exact segment_sound _ 142080 128 Update0277_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 142208 128 Update0277_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
