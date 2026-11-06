import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0450_0_checked : (List.range' 230400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0450_1_checked : (List.range' 230528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0450_2_checked : (List.range' 230656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0450_3_checked : (List.range' 230784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0450_range (index : Nat) (lower : 230400 ≤ index) (upper : index < 230912) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 230656 then
    if cut : index < 230528 then
      exact segment_sound _ 230400 128 Update0450_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 230528 128 Update0450_1_checked index (by omega) (by omega)
  else
    if cut : index < 230784 then
      exact segment_sound _ 230656 128 Update0450_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 230784 128 Update0450_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
