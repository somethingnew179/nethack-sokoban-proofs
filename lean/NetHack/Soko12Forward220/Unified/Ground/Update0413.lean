import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0413_0_checked : (List.range' 211456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0413_1_checked : (List.range' 211584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0413_2_checked : (List.range' 211712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0413_3_checked : (List.range' 211840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0413_range (index : Nat) (lower : 211456 ≤ index) (upper : index < 211968) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 211712 then
    if cut : index < 211584 then
      exact segment_sound _ 211456 128 Update0413_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 211584 128 Update0413_1_checked index (by omega) (by omega)
  else
    if cut : index < 211840 then
      exact segment_sound _ 211712 128 Update0413_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 211840 128 Update0413_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
