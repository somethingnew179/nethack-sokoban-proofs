import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0300_0_checked : (List.range' 153600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0300_1_checked : (List.range' 153728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0300_2_checked : (List.range' 153856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0300_3_checked : (List.range' 153984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0300_range (index : Nat) (lower : 153600 ≤ index) (upper : index < 154112) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 153856 then
    if cut : index < 153728 then
      exact segment_sound _ 153600 128 Update0300_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153728 128 Update0300_1_checked index (by omega) (by omega)
  else
    if cut : index < 153984 then
      exact segment_sound _ 153856 128 Update0300_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153984 128 Update0300_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
