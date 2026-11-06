import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0241_0_checked : (List.range' 123392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0241_1_checked : (List.range' 123520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0241_2_checked : (List.range' 123648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0241_3_checked : (List.range' 123776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0241_range (index : Nat) (lower : 123392 ≤ index) (upper : index < 123904) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 123648 then
    if cut : index < 123520 then
      exact segment_sound _ 123392 128 Update0241_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 123520 128 Update0241_1_checked index (by omega) (by omega)
  else
    if cut : index < 123776 then
      exact segment_sound _ 123648 128 Update0241_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 123776 128 Update0241_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
