import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0393_0_checked : (List.range' 201216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0393_1_checked : (List.range' 201344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0393_2_checked : (List.range' 201472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0393_3_checked : (List.range' 201600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0393_range (index : Nat) (lower : 201216 ≤ index) (upper : index < 201728) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 201472 then
    if cut : index < 201344 then
      exact segment_sound _ 201216 128 Update0393_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 201344 128 Update0393_1_checked index (by omega) (by omega)
  else
    if cut : index < 201600 then
      exact segment_sound _ 201472 128 Update0393_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 201600 128 Update0393_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
