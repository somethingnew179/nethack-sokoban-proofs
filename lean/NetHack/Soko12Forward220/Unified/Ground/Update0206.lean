import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0206_0_checked : (List.range' 105472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0206_1_checked : (List.range' 105600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0206_2_checked : (List.range' 105728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0206_3_checked : (List.range' 105856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0206_range (index : Nat) (lower : 105472 ≤ index) (upper : index < 105984) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 105728 then
    if cut : index < 105600 then
      exact segment_sound _ 105472 128 Update0206_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 105600 128 Update0206_1_checked index (by omega) (by omega)
  else
    if cut : index < 105856 then
      exact segment_sound _ 105728 128 Update0206_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 105856 128 Update0206_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
