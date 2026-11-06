import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0634_0_checked : (List.range' 324608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0634_1_checked : (List.range' 324736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0634_2_checked : (List.range' 324864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0634_3_checked : (List.range' 324992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0634_range (index : Nat) (lower : 324608 ≤ index) (upper : index < 325120) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 324864 then
    if cut : index < 324736 then
      exact segment_sound _ 324608 128 Update0634_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324736 128 Update0634_1_checked index (by omega) (by omega)
  else
    if cut : index < 324992 then
      exact segment_sound _ 324864 128 Update0634_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324992 128 Update0634_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
