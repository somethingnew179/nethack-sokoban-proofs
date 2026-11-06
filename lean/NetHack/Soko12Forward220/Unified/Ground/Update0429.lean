import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0429_0_checked : (List.range' 219648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0429_1_checked : (List.range' 219776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0429_2_checked : (List.range' 219904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0429_3_checked : (List.range' 220032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0429_range (index : Nat) (lower : 219648 ≤ index) (upper : index < 220160) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 219904 then
    if cut : index < 219776 then
      exact segment_sound _ 219648 128 Update0429_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219776 128 Update0429_1_checked index (by omega) (by omega)
  else
    if cut : index < 220032 then
      exact segment_sound _ 219904 128 Update0429_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220032 128 Update0429_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
