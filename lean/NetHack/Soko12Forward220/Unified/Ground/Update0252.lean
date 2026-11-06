import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0252_0_checked : (List.range' 129024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0252_1_checked : (List.range' 129152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0252_2_checked : (List.range' 129280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0252_3_checked : (List.range' 129408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0252_range (index : Nat) (lower : 129024 ≤ index) (upper : index < 129536) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 129280 then
    if cut : index < 129152 then
      exact segment_sound _ 129024 128 Update0252_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 129152 128 Update0252_1_checked index (by omega) (by omega)
  else
    if cut : index < 129408 then
      exact segment_sound _ 129280 128 Update0252_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 129408 128 Update0252_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
