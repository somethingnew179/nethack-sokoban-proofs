import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0291_0_checked : (List.range' 148992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0291_1_checked : (List.range' 149120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0291_2_checked : (List.range' 149248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0291_3_checked : (List.range' 149376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0291_range (index : Nat) (lower : 148992 ≤ index) (upper : index < 149504) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 149248 then
    if cut : index < 149120 then
      exact segment_sound _ 148992 128 Update0291_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149120 128 Update0291_1_checked index (by omega) (by omega)
  else
    if cut : index < 149376 then
      exact segment_sound _ 149248 128 Update0291_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 149376 128 Update0291_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
