import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0674_0_checked : (List.range' 345088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0674_1_checked : (List.range' 345216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0674_2_checked : (List.range' 345344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0674_3_checked : (List.range' 345472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0674_range (index : Nat) (lower : 345088 ≤ index) (upper : index < 345600) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 345344 then
    if cut : index < 345216 then
      exact segment_sound _ 345088 128 Update0674_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345216 128 Update0674_1_checked index (by omega) (by omega)
  else
    if cut : index < 345472 then
      exact segment_sound _ 345344 128 Update0674_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345472 128 Update0674_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
