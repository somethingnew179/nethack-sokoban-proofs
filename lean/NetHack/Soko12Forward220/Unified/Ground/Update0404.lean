import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0404_0_checked : (List.range' 206848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0404_1_checked : (List.range' 206976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0404_2_checked : (List.range' 207104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0404_3_checked : (List.range' 207232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0404_range (index : Nat) (lower : 206848 ≤ index) (upper : index < 207360) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 207104 then
    if cut : index < 206976 then
      exact segment_sound _ 206848 128 Update0404_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 206976 128 Update0404_1_checked index (by omega) (by omega)
  else
    if cut : index < 207232 then
      exact segment_sound _ 207104 128 Update0404_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 207232 128 Update0404_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
