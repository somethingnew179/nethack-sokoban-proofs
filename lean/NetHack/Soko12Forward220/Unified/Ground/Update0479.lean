import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0479_0_checked : (List.range' 245248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0479_1_checked : (List.range' 245376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0479_2_checked : (List.range' 245504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0479_3_checked : (List.range' 245632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0479_range (index : Nat) (lower : 245248 ≤ index) (upper : index < 245760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 245504 then
    if cut : index < 245376 then
      exact segment_sound _ 245248 128 Update0479_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 245376 128 Update0479_1_checked index (by omega) (by omega)
  else
    if cut : index < 245632 then
      exact segment_sound _ 245504 128 Update0479_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 245632 128 Update0479_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
