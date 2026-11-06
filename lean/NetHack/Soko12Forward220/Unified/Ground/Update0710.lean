import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0710_0_checked : (List.range' 363520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0710_1_checked : (List.range' 363648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0710_2_checked : (List.range' 363776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0710_3_checked : (List.range' 363904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0710_range (index : Nat) (lower : 363520 ≤ index) (upper : index < 364032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 363776 then
    if cut : index < 363648 then
      exact segment_sound _ 363520 128 Update0710_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363648 128 Update0710_1_checked index (by omega) (by omega)
  else
    if cut : index < 363904 then
      exact segment_sound _ 363776 128 Update0710_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363904 128 Update0710_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
