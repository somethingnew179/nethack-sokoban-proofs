import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0448_0_checked : (List.range' 229376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0448_1_checked : (List.range' 229504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0448_2_checked : (List.range' 229632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0448_3_checked : (List.range' 229760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0448_range (index : Nat) (lower : 229376 ≤ index) (upper : index < 229888) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 229632 then
    if cut : index < 229504 then
      exact segment_sound _ 229376 128 Update0448_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 229504 128 Update0448_1_checked index (by omega) (by omega)
  else
    if cut : index < 229760 then
      exact segment_sound _ 229632 128 Update0448_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 229760 128 Update0448_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
