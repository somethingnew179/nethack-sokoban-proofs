import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0503_0_checked : (List.range' 257536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0503_1_checked : (List.range' 257664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0503_2_checked : (List.range' 257792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0503_3_checked : (List.range' 257920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0503_range (index : Nat) (lower : 257536 ≤ index) (upper : index < 258048) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 257792 then
    if cut : index < 257664 then
      exact segment_sound _ 257536 128 Update0503_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 257664 128 Update0503_1_checked index (by omega) (by omega)
  else
    if cut : index < 257920 then
      exact segment_sound _ 257792 128 Update0503_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 257920 128 Update0503_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
