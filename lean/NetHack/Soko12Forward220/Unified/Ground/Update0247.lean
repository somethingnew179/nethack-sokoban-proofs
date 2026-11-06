import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0247_0_checked : (List.range' 126464 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0247_1_checked : (List.range' 126592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0247_2_checked : (List.range' 126720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0247_3_checked : (List.range' 126848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0247_range (index : Nat) (lower : 126464 ≤ index) (upper : index < 126976) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 126720 then
    if cut : index < 126592 then
      exact segment_sound _ 126464 128 Update0247_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 126592 128 Update0247_1_checked index (by omega) (by omega)
  else
    if cut : index < 126848 then
      exact segment_sound _ 126720 128 Update0247_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 126848 128 Update0247_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
