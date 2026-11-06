import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0434_0_checked : (List.range' 222208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0434_1_checked : (List.range' 222336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0434_2_checked : (List.range' 222464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0434_3_checked : (List.range' 222592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0434_range (index : Nat) (lower : 222208 ≤ index) (upper : index < 222720) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 222464 then
    if cut : index < 222336 then
      exact segment_sound _ 222208 128 Update0434_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 222336 128 Update0434_1_checked index (by omega) (by omega)
  else
    if cut : index < 222592 then
      exact segment_sound _ 222464 128 Update0434_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 222592 128 Update0434_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
