import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0210_0_checked : (List.range' 107520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0210_1_checked : (List.range' 107648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0210_2_checked : (List.range' 107776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0210_3_checked : (List.range' 107904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0210_range (index : Nat) (lower : 107520 ≤ index) (upper : index < 108032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 107776 then
    if cut : index < 107648 then
      exact segment_sound _ 107520 128 Update0210_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 107648 128 Update0210_1_checked index (by omega) (by omega)
  else
    if cut : index < 107904 then
      exact segment_sound _ 107776 128 Update0210_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 107904 128 Update0210_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
