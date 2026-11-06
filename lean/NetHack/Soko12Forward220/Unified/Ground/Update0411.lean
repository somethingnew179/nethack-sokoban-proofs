import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0411_0_checked : (List.range' 210432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0411_1_checked : (List.range' 210560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0411_2_checked : (List.range' 210688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0411_3_checked : (List.range' 210816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0411_range (index : Nat) (lower : 210432 ≤ index) (upper : index < 210944) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 210688 then
    if cut : index < 210560 then
      exact segment_sound _ 210432 128 Update0411_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 210560 128 Update0411_1_checked index (by omega) (by omega)
  else
    if cut : index < 210816 then
      exact segment_sound _ 210688 128 Update0411_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 210816 128 Update0411_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
