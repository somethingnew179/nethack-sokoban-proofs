import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0629_0_checked : (List.range' 322048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0629_1_checked : (List.range' 322176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0629_2_checked : (List.range' 322304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0629_3_checked : (List.range' 322432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0629_range (index : Nat) (lower : 322048 ≤ index) (upper : index < 322560) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 322304 then
    if cut : index < 322176 then
      exact segment_sound _ 322048 128 Update0629_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 322176 128 Update0629_1_checked index (by omega) (by omega)
  else
    if cut : index < 322432 then
      exact segment_sound _ 322304 128 Update0629_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 322432 128 Update0629_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
