import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0045_0_checked : (List.range' 23040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0045_1_checked : (List.range' 23168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0045_2_checked : (List.range' 23296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0045_3_checked : (List.range' 23424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0045_range (index : Nat) (lower : 23040 ≤ index) (upper : index < 23552) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 23296 then
    if cut : index < 23168 then
      exact segment_sound _ 23040 128 Update0045_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23168 128 Update0045_1_checked index (by omega) (by omega)
  else
    if cut : index < 23424 then
      exact segment_sound _ 23296 128 Update0045_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23424 128 Update0045_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
