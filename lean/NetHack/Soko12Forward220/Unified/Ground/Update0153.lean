import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0153_0_checked : (List.range' 78336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0153_1_checked : (List.range' 78464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0153_2_checked : (List.range' 78592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0153_3_checked : (List.range' 78720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0153_range (index : Nat) (lower : 78336 ≤ index) (upper : index < 78848) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 78592 then
    if cut : index < 78464 then
      exact segment_sound _ 78336 128 Update0153_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 78464 128 Update0153_1_checked index (by omega) (by omega)
  else
    if cut : index < 78720 then
      exact segment_sound _ 78592 128 Update0153_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 78720 128 Update0153_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
