import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0276_0_checked : (List.range' 141312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0276_1_checked : (List.range' 141440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0276_2_checked : (List.range' 141568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0276_3_checked : (List.range' 141696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0276_range (index : Nat) (lower : 141312 ≤ index) (upper : index < 141824) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 141568 then
    if cut : index < 141440 then
      exact segment_sound _ 141312 128 Update0276_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141440 128 Update0276_1_checked index (by omega) (by omega)
  else
    if cut : index < 141696 then
      exact segment_sound _ 141568 128 Update0276_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 141696 128 Update0276_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
