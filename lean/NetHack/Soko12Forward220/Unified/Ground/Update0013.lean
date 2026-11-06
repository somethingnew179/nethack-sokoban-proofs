import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0013_0_checked : (List.range' 6656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0013_1_checked : (List.range' 6784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0013_2_checked : (List.range' 6912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0013_3_checked : (List.range' 7040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0013_range (index : Nat) (lower : 6656 ≤ index) (upper : index < 7168) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 6912 then
    if cut : index < 6784 then
      exact segment_sound _ 6656 128 Update0013_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 6784 128 Update0013_1_checked index (by omega) (by omega)
  else
    if cut : index < 7040 then
      exact segment_sound _ 6912 128 Update0013_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 7040 128 Update0013_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
