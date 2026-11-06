import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0500_0_checked : (List.range' 256000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0500_1_checked : (List.range' 256128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0500_2_checked : (List.range' 256256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0500_3_checked : (List.range' 256384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0500_range (index : Nat) (lower : 256000 ≤ index) (upper : index < 256512) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 256256 then
    if cut : index < 256128 then
      exact segment_sound _ 256000 128 Update0500_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 256128 128 Update0500_1_checked index (by omega) (by omega)
  else
    if cut : index < 256384 then
      exact segment_sound _ 256256 128 Update0500_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 256384 128 Update0500_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
