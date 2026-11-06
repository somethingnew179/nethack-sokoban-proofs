import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0137_0_checked : (List.range' 70144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0137_1_checked : (List.range' 70272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0137_2_checked : (List.range' 70400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0137_3_checked : (List.range' 70528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0137_range (index : Nat) (lower : 70144 ≤ index) (upper : index < 70656) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 70400 then
    if cut : index < 70272 then
      exact segment_sound _ 70144 128 Update0137_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 70272 128 Update0137_1_checked index (by omega) (by omega)
  else
    if cut : index < 70528 then
      exact segment_sound _ 70400 128 Update0137_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 70528 128 Update0137_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
