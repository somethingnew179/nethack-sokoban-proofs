import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0489_0_checked : (List.range' 250368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0489_1_checked : (List.range' 250496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0489_2_checked : (List.range' 250624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0489_3_checked : (List.range' 250752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0489_range (index : Nat) (lower : 250368 ≤ index) (upper : index < 250880) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 250624 then
    if cut : index < 250496 then
      exact segment_sound _ 250368 128 Update0489_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 250496 128 Update0489_1_checked index (by omega) (by omega)
  else
    if cut : index < 250752 then
      exact segment_sound _ 250624 128 Update0489_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 250752 128 Update0489_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
