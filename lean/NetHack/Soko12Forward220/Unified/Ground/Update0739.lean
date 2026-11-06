import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0739_0_checked : (List.range' 378368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0739_1_checked : (List.range' 378496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0739_2_checked : (List.range' 378624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0739_3_checked : (List.range' 378752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0739_range (index : Nat) (lower : 378368 ≤ index) (upper : index < 378880) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 378624 then
    if cut : index < 378496 then
      exact segment_sound _ 378368 128 Update0739_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 378496 128 Update0739_1_checked index (by omega) (by omega)
  else
    if cut : index < 378752 then
      exact segment_sound _ 378624 128 Update0739_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 378752 128 Update0739_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
