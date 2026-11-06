import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0236_0_checked : (List.range' 120832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0236_1_checked : (List.range' 120960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0236_2_checked : (List.range' 121088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0236_3_checked : (List.range' 121216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0236_range (index : Nat) (lower : 120832 ≤ index) (upper : index < 121344) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 121088 then
    if cut : index < 120960 then
      exact segment_sound _ 120832 128 Update0236_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 120960 128 Update0236_1_checked index (by omega) (by omega)
  else
    if cut : index < 121216 then
      exact segment_sound _ 121088 128 Update0236_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 121216 128 Update0236_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
