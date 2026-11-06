import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0118_0_checked : (List.range' 60416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0118_1_checked : (List.range' 60544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0118_2_checked : (List.range' 60672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0118_3_checked : (List.range' 60800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0118_range (index : Nat) (lower : 60416 ≤ index) (upper : index < 60928) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 60672 then
    if cut : index < 60544 then
      exact segment_sound _ 60416 128 Update0118_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60544 128 Update0118_1_checked index (by omega) (by omega)
  else
    if cut : index < 60800 then
      exact segment_sound _ 60672 128 Update0118_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 60800 128 Update0118_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
