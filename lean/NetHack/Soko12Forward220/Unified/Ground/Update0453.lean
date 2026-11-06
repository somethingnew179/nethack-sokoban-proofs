import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0453_0_checked : (List.range' 231936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0453_1_checked : (List.range' 232064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0453_2_checked : (List.range' 232192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0453_3_checked : (List.range' 232320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0453_range (index : Nat) (lower : 231936 ≤ index) (upper : index < 232448) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 232192 then
    if cut : index < 232064 then
      exact segment_sound _ 231936 128 Update0453_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232064 128 Update0453_1_checked index (by omega) (by omega)
  else
    if cut : index < 232320 then
      exact segment_sound _ 232192 128 Update0453_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 232320 128 Update0453_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
