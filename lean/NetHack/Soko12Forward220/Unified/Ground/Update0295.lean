import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0295_0_checked : (List.range' 151040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0295_1_checked : (List.range' 151168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0295_2_checked : (List.range' 151296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0295_3_checked : (List.range' 151424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0295_range (index : Nat) (lower : 151040 ≤ index) (upper : index < 151552) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 151296 then
    if cut : index < 151168 then
      exact segment_sound _ 151040 128 Update0295_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151168 128 Update0295_1_checked index (by omega) (by omega)
  else
    if cut : index < 151424 then
      exact segment_sound _ 151296 128 Update0295_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 151424 128 Update0295_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
