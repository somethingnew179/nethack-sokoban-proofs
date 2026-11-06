import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0054_0_checked : (List.range' 27648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0054_1_checked : (List.range' 27776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0054_2_checked : (List.range' 27904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0054_3_checked : (List.range' 28032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0054_range (index : Nat) (lower : 27648 ≤ index) (upper : index < 28160) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 27904 then
    if cut : index < 27776 then
      exact segment_sound _ 27648 128 Update0054_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27776 128 Update0054_1_checked index (by omega) (by omega)
  else
    if cut : index < 28032 then
      exact segment_sound _ 27904 128 Update0054_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 28032 128 Update0054_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
