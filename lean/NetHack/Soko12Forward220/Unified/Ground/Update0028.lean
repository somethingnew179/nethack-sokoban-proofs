import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0028_0_checked : (List.range' 14336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0028_1_checked : (List.range' 14464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0028_2_checked : (List.range' 14592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0028_3_checked : (List.range' 14720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0028_range (index : Nat) (lower : 14336 ≤ index) (upper : index < 14848) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 14592 then
    if cut : index < 14464 then
      exact segment_sound _ 14336 128 Update0028_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 14464 128 Update0028_1_checked index (by omega) (by omega)
  else
    if cut : index < 14720 then
      exact segment_sound _ 14592 128 Update0028_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 14720 128 Update0028_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
