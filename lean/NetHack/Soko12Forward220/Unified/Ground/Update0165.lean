import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0165_0_checked : (List.range' 84480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0165_1_checked : (List.range' 84608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0165_2_checked : (List.range' 84736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0165_3_checked : (List.range' 84864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0165_range (index : Nat) (lower : 84480 ≤ index) (upper : index < 84992) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 84736 then
    if cut : index < 84608 then
      exact segment_sound _ 84480 128 Update0165_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 84608 128 Update0165_1_checked index (by omega) (by omega)
  else
    if cut : index < 84864 then
      exact segment_sound _ 84736 128 Update0165_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 84864 128 Update0165_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
