import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0707_0_checked : (List.range' 361984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0707_1_checked : (List.range' 362112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0707_2_checked : (List.range' 362240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0707_3_checked : (List.range' 362368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0707_range (index : Nat) (lower : 361984 ≤ index) (upper : index < 362496) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 362240 then
    if cut : index < 362112 then
      exact segment_sound _ 361984 128 Update0707_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 362112 128 Update0707_1_checked index (by omega) (by omega)
  else
    if cut : index < 362368 then
      exact segment_sound _ 362240 128 Update0707_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 362368 128 Update0707_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
