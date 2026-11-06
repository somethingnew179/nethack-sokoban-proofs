import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0332_0_checked : (List.range' 169984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0332_1_checked : (List.range' 170112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0332_2_checked : (List.range' 170240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0332_3_checked : (List.range' 170368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0332_range (index : Nat) (lower : 169984 ≤ index) (upper : index < 170496) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 170240 then
    if cut : index < 170112 then
      exact segment_sound _ 169984 128 Update0332_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 170112 128 Update0332_1_checked index (by omega) (by omega)
  else
    if cut : index < 170368 then
      exact segment_sound _ 170240 128 Update0332_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 170368 128 Update0332_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
