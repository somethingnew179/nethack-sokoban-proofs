import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0018_0_checked : (List.range' 9216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0018_1_checked : (List.range' 9344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0018_2_checked : (List.range' 9472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0018_3_checked : (List.range' 9600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0018_range (index : Nat) (lower : 9216 ≤ index) (upper : index < 9728) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 9472 then
    if cut : index < 9344 then
      exact segment_sound _ 9216 128 Update0018_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9344 128 Update0018_1_checked index (by omega) (by omega)
  else
    if cut : index < 9600 then
      exact segment_sound _ 9472 128 Update0018_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 9600 128 Update0018_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
