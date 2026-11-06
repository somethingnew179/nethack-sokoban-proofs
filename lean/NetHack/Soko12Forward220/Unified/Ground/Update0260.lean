import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0260_0_checked : (List.range' 133120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0260_1_checked : (List.range' 133248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0260_2_checked : (List.range' 133376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0260_3_checked : (List.range' 133504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0260_range (index : Nat) (lower : 133120 ≤ index) (upper : index < 133632) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 133376 then
    if cut : index < 133248 then
      exact segment_sound _ 133120 128 Update0260_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 133248 128 Update0260_1_checked index (by omega) (by omega)
  else
    if cut : index < 133504 then
      exact segment_sound _ 133376 128 Update0260_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 133504 128 Update0260_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
