import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0239_0_checked : (List.range' 122368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0239_1_checked : (List.range' 122496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0239_2_checked : (List.range' 122624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0239_3_checked : (List.range' 122752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0239_range (index : Nat) (lower : 122368 ≤ index) (upper : index < 122880) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 122624 then
    if cut : index < 122496 then
      exact segment_sound _ 122368 128 Update0239_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 122496 128 Update0239_1_checked index (by omega) (by omega)
  else
    if cut : index < 122752 then
      exact segment_sound _ 122624 128 Update0239_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 122752 128 Update0239_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
