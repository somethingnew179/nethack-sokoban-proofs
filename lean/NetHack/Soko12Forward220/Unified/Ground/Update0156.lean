import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0156_0_checked : (List.range' 79872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0156_1_checked : (List.range' 80000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0156_2_checked : (List.range' 80128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0156_3_checked : (List.range' 80256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0156_range (index : Nat) (lower : 79872 ≤ index) (upper : index < 80384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 80128 then
    if cut : index < 80000 then
      exact segment_sound _ 79872 128 Update0156_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80000 128 Update0156_1_checked index (by omega) (by omega)
  else
    if cut : index < 80256 then
      exact segment_sound _ 80128 128 Update0156_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80256 128 Update0156_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
