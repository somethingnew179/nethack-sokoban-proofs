import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0460_0_checked : (List.range' 235520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0460_1_checked : (List.range' 235648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0460_2_checked : (List.range' 235776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0460_3_checked : (List.range' 235904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0460_range (index : Nat) (lower : 235520 ≤ index) (upper : index < 236032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 235776 then
    if cut : index < 235648 then
      exact segment_sound _ 235520 128 Update0460_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 235648 128 Update0460_1_checked index (by omega) (by omega)
  else
    if cut : index < 235904 then
      exact segment_sound _ 235776 128 Update0460_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 235904 128 Update0460_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
