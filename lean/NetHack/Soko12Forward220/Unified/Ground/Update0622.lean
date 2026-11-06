import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0622_0_checked : (List.range' 318464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0622_1_checked : (List.range' 318592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0622_2_checked : (List.range' 318720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0622_3_checked : (List.range' 318848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0622_range (index : Nat) (lower : 318464 ≤ index) (upper : index < 318976) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 318720 then
    if cut : index < 318592 then
      exact segment_sound _ 318464 128 Update0622_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 318592 128 Update0622_1_checked index (by omega) (by omega)
  else
    if cut : index < 318848 then
      exact segment_sound _ 318720 128 Update0622_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 318848 128 Update0622_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
