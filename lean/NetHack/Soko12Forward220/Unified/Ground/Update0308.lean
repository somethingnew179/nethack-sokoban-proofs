import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0308_0_checked : (List.range' 157696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0308_1_checked : (List.range' 157824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0308_2_checked : (List.range' 157952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0308_3_checked : (List.range' 158080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0308_range (index : Nat) (lower : 157696 ≤ index) (upper : index < 158208) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 157952 then
    if cut : index < 157824 then
      exact segment_sound _ 157696 128 Update0308_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 157824 128 Update0308_1_checked index (by omega) (by omega)
  else
    if cut : index < 158080 then
      exact segment_sound _ 157952 128 Update0308_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 158080 128 Update0308_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
