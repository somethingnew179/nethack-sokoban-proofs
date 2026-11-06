import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0395_0_checked : (List.range' 202240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0395_1_checked : (List.range' 202368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0395_2_checked : (List.range' 202496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0395_3_checked : (List.range' 202624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0395_range (index : Nat) (lower : 202240 ≤ index) (upper : index < 202752) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 202496 then
    if cut : index < 202368 then
      exact segment_sound _ 202240 128 Update0395_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 202368 128 Update0395_1_checked index (by omega) (by omega)
  else
    if cut : index < 202624 then
      exact segment_sound _ 202496 128 Update0395_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 202624 128 Update0395_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
