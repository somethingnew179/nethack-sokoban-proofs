import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0321_0_checked : (List.range' 164352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0321_1_checked : (List.range' 164480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0321_2_checked : (List.range' 164608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0321_3_checked : (List.range' 164736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0321_range (index : Nat) (lower : 164352 ≤ index) (upper : index < 164864) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 164608 then
    if cut : index < 164480 then
      exact segment_sound _ 164352 128 Update0321_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164480 128 Update0321_1_checked index (by omega) (by omega)
  else
    if cut : index < 164736 then
      exact segment_sound _ 164608 128 Update0321_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164736 128 Update0321_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
