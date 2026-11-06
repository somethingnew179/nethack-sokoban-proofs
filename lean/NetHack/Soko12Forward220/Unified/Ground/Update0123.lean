import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0123_0_checked : (List.range' 62976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0123_1_checked : (List.range' 63104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0123_2_checked : (List.range' 63232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0123_3_checked : (List.range' 63360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0123_range (index : Nat) (lower : 62976 ≤ index) (upper : index < 63488) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 63232 then
    if cut : index < 63104 then
      exact segment_sound _ 62976 128 Update0123_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 63104 128 Update0123_1_checked index (by omega) (by omega)
  else
    if cut : index < 63360 then
      exact segment_sound _ 63232 128 Update0123_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 63360 128 Update0123_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
