import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0352_0_checked : (List.range' 180224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0352_1_checked : (List.range' 180352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0352_2_checked : (List.range' 180480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0352_3_checked : (List.range' 180608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0352_range (index : Nat) (lower : 180224 ≤ index) (upper : index < 180736) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 180480 then
    if cut : index < 180352 then
      exact segment_sound _ 180224 128 Update0352_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180352 128 Update0352_1_checked index (by omega) (by omega)
  else
    if cut : index < 180608 then
      exact segment_sound _ 180480 128 Update0352_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180608 128 Update0352_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
