import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0181_0_checked : (List.range' 92672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0181_1_checked : (List.range' 92800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0181_2_checked : (List.range' 92928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0181_3_checked : (List.range' 93056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0181_range (index : Nat) (lower : 92672 ≤ index) (upper : index < 93184) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 92928 then
    if cut : index < 92800 then
      exact segment_sound _ 92672 128 Update0181_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 92800 128 Update0181_1_checked index (by omega) (by omega)
  else
    if cut : index < 93056 then
      exact segment_sound _ 92928 128 Update0181_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 93056 128 Update0181_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
