import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0281_0_checked : (List.range' 143872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0281_1_checked : (List.range' 144000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0281_2_checked : (List.range' 144128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0281_3_checked : (List.range' 144256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0281_range (index : Nat) (lower : 143872 ≤ index) (upper : index < 144384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 144128 then
    if cut : index < 144000 then
      exact segment_sound _ 143872 128 Update0281_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 144000 128 Update0281_1_checked index (by omega) (by omega)
  else
    if cut : index < 144256 then
      exact segment_sound _ 144128 128 Update0281_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 144256 128 Update0281_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
