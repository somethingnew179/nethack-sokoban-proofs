import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0041_0_checked : (List.range' 20992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0041_1_checked : (List.range' 21120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0041_2_checked : (List.range' 21248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0041_3_checked : (List.range' 21376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0041_range (index : Nat) (lower : 20992 ≤ index) (upper : index < 21504) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 21248 then
    if cut : index < 21120 then
      exact segment_sound _ 20992 128 Update0041_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 21120 128 Update0041_1_checked index (by omega) (by omega)
  else
    if cut : index < 21376 then
      exact segment_sound _ 21248 128 Update0041_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 21376 128 Update0041_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
