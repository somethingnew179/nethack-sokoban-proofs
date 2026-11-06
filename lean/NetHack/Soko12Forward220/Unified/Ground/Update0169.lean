import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0169_0_checked : (List.range' 86528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0169_1_checked : (List.range' 86656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0169_2_checked : (List.range' 86784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0169_3_checked : (List.range' 86912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0169_range (index : Nat) (lower : 86528 ≤ index) (upper : index < 87040) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 86784 then
    if cut : index < 86656 then
      exact segment_sound _ 86528 128 Update0169_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 86656 128 Update0169_1_checked index (by omega) (by omega)
  else
    if cut : index < 86912 then
      exact segment_sound _ 86784 128 Update0169_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 86912 128 Update0169_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
