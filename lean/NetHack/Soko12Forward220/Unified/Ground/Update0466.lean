import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0466_0_checked : (List.range' 238592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0466_1_checked : (List.range' 238720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0466_2_checked : (List.range' 238848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0466_3_checked : (List.range' 238976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0466_range (index : Nat) (lower : 238592 ≤ index) (upper : index < 239104) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 238848 then
    if cut : index < 238720 then
      exact segment_sound _ 238592 128 Update0466_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 238720 128 Update0466_1_checked index (by omega) (by omega)
  else
    if cut : index < 238976 then
      exact segment_sound _ 238848 128 Update0466_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 238976 128 Update0466_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
