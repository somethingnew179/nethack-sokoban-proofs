import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0642_0_checked : (List.range' 328704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0642_1_checked : (List.range' 328832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0642_2_checked : (List.range' 328960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0642_3_checked : (List.range' 329088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0642_range (index : Nat) (lower : 328704 ≤ index) (upper : index < 329216) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 328960 then
    if cut : index < 328832 then
      exact segment_sound _ 328704 128 Update0642_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 328832 128 Update0642_1_checked index (by omega) (by omega)
  else
    if cut : index < 329088 then
      exact segment_sound _ 328960 128 Update0642_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 329088 128 Update0642_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
