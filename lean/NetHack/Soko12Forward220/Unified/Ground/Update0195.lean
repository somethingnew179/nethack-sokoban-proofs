import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0195_0_checked : (List.range' 99840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0195_1_checked : (List.range' 99968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0195_2_checked : (List.range' 100096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0195_3_checked : (List.range' 100224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0195_range (index : Nat) (lower : 99840 ≤ index) (upper : index < 100352) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 100096 then
    if cut : index < 99968 then
      exact segment_sound _ 99840 128 Update0195_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 99968 128 Update0195_1_checked index (by omega) (by omega)
  else
    if cut : index < 100224 then
      exact segment_sound _ 100096 128 Update0195_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 100224 128 Update0195_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
