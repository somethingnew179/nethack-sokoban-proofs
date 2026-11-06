import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0607_0_checked : (List.range' 310784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0607_1_checked : (List.range' 310912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0607_2_checked : (List.range' 311040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0607_3_checked : (List.range' 311168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0607_range (index : Nat) (lower : 310784 ≤ index) (upper : index < 311296) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 311040 then
    if cut : index < 310912 then
      exact segment_sound _ 310784 128 Update0607_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 310912 128 Update0607_1_checked index (by omega) (by omega)
  else
    if cut : index < 311168 then
      exact segment_sound _ 311040 128 Update0607_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 311168 128 Update0607_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
