import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0323_0_checked : (List.range' 165376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0323_1_checked : (List.range' 165504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0323_2_checked : (List.range' 165632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0323_3_checked : (List.range' 165760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0323_range (index : Nat) (lower : 165376 ≤ index) (upper : index < 165888) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 165632 then
    if cut : index < 165504 then
      exact segment_sound _ 165376 128 Update0323_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 165504 128 Update0323_1_checked index (by omega) (by omega)
  else
    if cut : index < 165760 then
      exact segment_sound _ 165632 128 Update0323_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 165760 128 Update0323_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
