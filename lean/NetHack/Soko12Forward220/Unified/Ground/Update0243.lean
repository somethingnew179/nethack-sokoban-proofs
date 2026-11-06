import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0243_0_checked : (List.range' 124416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0243_1_checked : (List.range' 124544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0243_2_checked : (List.range' 124672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0243_3_checked : (List.range' 124800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0243_range (index : Nat) (lower : 124416 ≤ index) (upper : index < 124928) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 124672 then
    if cut : index < 124544 then
      exact segment_sound _ 124416 128 Update0243_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 124544 128 Update0243_1_checked index (by omega) (by omega)
  else
    if cut : index < 124800 then
      exact segment_sound _ 124672 128 Update0243_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 124800 128 Update0243_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
