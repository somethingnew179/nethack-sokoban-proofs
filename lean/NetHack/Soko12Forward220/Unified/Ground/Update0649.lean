import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0649_0_checked : (List.range' 332288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0649_1_checked : (List.range' 332416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0649_2_checked : (List.range' 332544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0649_3_checked : (List.range' 332672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0649_range (index : Nat) (lower : 332288 ≤ index) (upper : index < 332800) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 332544 then
    if cut : index < 332416 then
      exact segment_sound _ 332288 128 Update0649_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 332416 128 Update0649_1_checked index (by omega) (by omega)
  else
    if cut : index < 332672 then
      exact segment_sound _ 332544 128 Update0649_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 332672 128 Update0649_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
