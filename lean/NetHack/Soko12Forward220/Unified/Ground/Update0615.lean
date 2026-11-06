import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0615_0_checked : (List.range' 314880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0615_1_checked : (List.range' 315008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0615_2_checked : (List.range' 315136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0615_3_checked : (List.range' 315264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0615_range (index : Nat) (lower : 314880 ≤ index) (upper : index < 315392) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 315136 then
    if cut : index < 315008 then
      exact segment_sound _ 314880 128 Update0615_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 315008 128 Update0615_1_checked index (by omega) (by omega)
  else
    if cut : index < 315264 then
      exact segment_sound _ 315136 128 Update0615_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 315264 128 Update0615_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
