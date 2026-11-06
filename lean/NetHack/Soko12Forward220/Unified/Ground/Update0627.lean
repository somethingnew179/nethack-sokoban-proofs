import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0627_0_checked : (List.range' 321024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0627_1_checked : (List.range' 321152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0627_2_checked : (List.range' 321280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0627_3_checked : (List.range' 321408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0627_range (index : Nat) (lower : 321024 ≤ index) (upper : index < 321536) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 321280 then
    if cut : index < 321152 then
      exact segment_sound _ 321024 128 Update0627_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 321152 128 Update0627_1_checked index (by omega) (by omega)
  else
    if cut : index < 321408 then
      exact segment_sound _ 321280 128 Update0627_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 321408 128 Update0627_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
