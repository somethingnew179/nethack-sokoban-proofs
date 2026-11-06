import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0658_0_checked : (List.range' 336896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0658_1_checked : (List.range' 337024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0658_2_checked : (List.range' 337152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0658_3_checked : (List.range' 337280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0658_range (index : Nat) (lower : 336896 ≤ index) (upper : index < 337408) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 337152 then
    if cut : index < 337024 then
      exact segment_sound _ 336896 128 Update0658_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 337024 128 Update0658_1_checked index (by omega) (by omega)
  else
    if cut : index < 337280 then
      exact segment_sound _ 337152 128 Update0658_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 337280 128 Update0658_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
