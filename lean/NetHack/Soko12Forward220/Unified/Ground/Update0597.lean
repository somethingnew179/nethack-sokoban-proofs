import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0597_0_checked : (List.range' 305664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0597_1_checked : (List.range' 305792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0597_2_checked : (List.range' 305920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0597_3_checked : (List.range' 306048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0597_range (index : Nat) (lower : 305664 ≤ index) (upper : index < 306176) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 305920 then
    if cut : index < 305792 then
      exact segment_sound _ 305664 128 Update0597_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 305792 128 Update0597_1_checked index (by omega) (by omega)
  else
    if cut : index < 306048 then
      exact segment_sound _ 305920 128 Update0597_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306048 128 Update0597_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
