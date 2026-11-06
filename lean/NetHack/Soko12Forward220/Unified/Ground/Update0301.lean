import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0301_0_checked : (List.range' 154112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0301_1_checked : (List.range' 154240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0301_2_checked : (List.range' 154368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0301_3_checked : (List.range' 154496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0301_range (index : Nat) (lower : 154112 ≤ index) (upper : index < 154624) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 154368 then
    if cut : index < 154240 then
      exact segment_sound _ 154112 128 Update0301_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 154240 128 Update0301_1_checked index (by omega) (by omega)
  else
    if cut : index < 154496 then
      exact segment_sound _ 154368 128 Update0301_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 154496 128 Update0301_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
