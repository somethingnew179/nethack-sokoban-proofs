import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0008_0_checked : (List.range' 4096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0008_1_checked : (List.range' 4224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0008_2_checked : (List.range' 4352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0008_3_checked : (List.range' 4480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0008_range (index : Nat) (lower : 4096 ≤ index) (upper : index < 4608) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 4352 then
    if cut : index < 4224 then
      exact segment_sound _ 4096 128 Update0008_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 4224 128 Update0008_1_checked index (by omega) (by omega)
  else
    if cut : index < 4480 then
      exact segment_sound _ 4352 128 Update0008_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 4480 128 Update0008_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
