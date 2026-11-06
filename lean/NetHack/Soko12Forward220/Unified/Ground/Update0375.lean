import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0375_0_checked : (List.range' 192000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0375_1_checked : (List.range' 192128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0375_2_checked : (List.range' 192256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0375_3_checked : (List.range' 192384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0375_range (index : Nat) (lower : 192000 ≤ index) (upper : index < 192512) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 192256 then
    if cut : index < 192128 then
      exact segment_sound _ 192000 128 Update0375_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 192128 128 Update0375_1_checked index (by omega) (by omega)
  else
    if cut : index < 192384 then
      exact segment_sound _ 192256 128 Update0375_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 192384 128 Update0375_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
