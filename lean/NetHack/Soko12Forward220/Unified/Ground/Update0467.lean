import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0467_0_checked : (List.range' 239104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0467_1_checked : (List.range' 239232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0467_2_checked : (List.range' 239360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0467_3_checked : (List.range' 239488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0467_range (index : Nat) (lower : 239104 ≤ index) (upper : index < 239616) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 239360 then
    if cut : index < 239232 then
      exact segment_sound _ 239104 128 Update0467_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 239232 128 Update0467_1_checked index (by omega) (by omega)
  else
    if cut : index < 239488 then
      exact segment_sound _ 239360 128 Update0467_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 239488 128 Update0467_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
