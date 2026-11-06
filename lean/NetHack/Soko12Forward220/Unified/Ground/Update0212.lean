import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0212_0_checked : (List.range' 108544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0212_1_checked : (List.range' 108672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0212_2_checked : (List.range' 108800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0212_3_checked : (List.range' 108928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0212_range (index : Nat) (lower : 108544 ≤ index) (upper : index < 109056) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 108800 then
    if cut : index < 108672 then
      exact segment_sound _ 108544 128 Update0212_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 108672 128 Update0212_1_checked index (by omega) (by omega)
  else
    if cut : index < 108928 then
      exact segment_sound _ 108800 128 Update0212_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 108928 128 Update0212_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
