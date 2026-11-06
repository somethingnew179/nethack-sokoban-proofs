import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0420_0_checked : (List.range' 215040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0420_1_checked : (List.range' 215168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0420_2_checked : (List.range' 215296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0420_3_checked : (List.range' 215424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0420_range (index : Nat) (lower : 215040 ≤ index) (upper : index < 215552) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 215296 then
    if cut : index < 215168 then
      exact segment_sound _ 215040 128 Update0420_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 215168 128 Update0420_1_checked index (by omega) (by omega)
  else
    if cut : index < 215424 then
      exact segment_sound _ 215296 128 Update0420_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 215424 128 Update0420_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
