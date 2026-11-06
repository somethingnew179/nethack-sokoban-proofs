import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0085_0_checked : (List.range' 43520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0085_1_checked : (List.range' 43648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0085_2_checked : (List.range' 43776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0085_3_checked : (List.range' 43904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0085_range (index : Nat) (lower : 43520 ≤ index) (upper : index < 44032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 43776 then
    if cut : index < 43648 then
      exact segment_sound _ 43520 128 Update0085_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 43648 128 Update0085_1_checked index (by omega) (by omega)
  else
    if cut : index < 43904 then
      exact segment_sound _ 43776 128 Update0085_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 43904 128 Update0085_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
