import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0585_0_checked : (List.range' 299520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0585_1_checked : (List.range' 299648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0585_2_checked : (List.range' 299776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0585_3_checked : (List.range' 299904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0585_range (index : Nat) (lower : 299520 ≤ index) (upper : index < 300032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 299776 then
    if cut : index < 299648 then
      exact segment_sound _ 299520 128 Update0585_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 299648 128 Update0585_1_checked index (by omega) (by omega)
  else
    if cut : index < 299904 then
      exact segment_sound _ 299776 128 Update0585_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 299904 128 Update0585_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
