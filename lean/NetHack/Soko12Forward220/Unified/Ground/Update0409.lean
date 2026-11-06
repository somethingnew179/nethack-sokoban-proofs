import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0409_0_checked : (List.range' 209408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0409_1_checked : (List.range' 209536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0409_2_checked : (List.range' 209664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0409_3_checked : (List.range' 209792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0409_range (index : Nat) (lower : 209408 ≤ index) (upper : index < 209920) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 209664 then
    if cut : index < 209536 then
      exact segment_sound _ 209408 128 Update0409_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209536 128 Update0409_1_checked index (by omega) (by omega)
  else
    if cut : index < 209792 then
      exact segment_sound _ 209664 128 Update0409_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 209792 128 Update0409_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
