import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0121_0_checked : (List.range' 61952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0121_1_checked : (List.range' 62080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0121_2_checked : (List.range' 62208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0121_3_checked : (List.range' 62336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0121_range (index : Nat) (lower : 61952 ≤ index) (upper : index < 62464) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 62208 then
    if cut : index < 62080 then
      exact segment_sound _ 61952 128 Update0121_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 62080 128 Update0121_1_checked index (by omega) (by omega)
  else
    if cut : index < 62336 then
      exact segment_sound _ 62208 128 Update0121_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 62336 128 Update0121_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
