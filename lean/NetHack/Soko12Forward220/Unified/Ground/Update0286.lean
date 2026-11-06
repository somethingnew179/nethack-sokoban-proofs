import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0286_0_checked : (List.range' 146432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0286_1_checked : (List.range' 146560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0286_2_checked : (List.range' 146688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0286_3_checked : (List.range' 146816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0286_range (index : Nat) (lower : 146432 ≤ index) (upper : index < 146944) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 146688 then
    if cut : index < 146560 then
      exact segment_sound _ 146432 128 Update0286_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 146560 128 Update0286_1_checked index (by omega) (by omega)
  else
    if cut : index < 146816 then
      exact segment_sound _ 146688 128 Update0286_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 146816 128 Update0286_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
