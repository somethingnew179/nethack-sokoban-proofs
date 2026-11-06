import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0612_0_checked : (List.range' 313344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0612_1_checked : (List.range' 313472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0612_2_checked : (List.range' 313600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0612_3_checked : (List.range' 313728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0612_range (index : Nat) (lower : 313344 ≤ index) (upper : index < 313856) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 313600 then
    if cut : index < 313472 then
      exact segment_sound _ 313344 128 Update0612_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 313472 128 Update0612_1_checked index (by omega) (by omega)
  else
    if cut : index < 313728 then
      exact segment_sound _ 313600 128 Update0612_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 313728 128 Update0612_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
