import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0552_0_checked : (List.range' 282624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0552_1_checked : (List.range' 282752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0552_2_checked : (List.range' 282880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0552_3_checked : (List.range' 283008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0552_range (index : Nat) (lower : 282624 ≤ index) (upper : index < 283136) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 282880 then
    if cut : index < 282752 then
      exact segment_sound _ 282624 128 Update0552_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 282752 128 Update0552_1_checked index (by omega) (by omega)
  else
    if cut : index < 283008 then
      exact segment_sound _ 282880 128 Update0552_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 283008 128 Update0552_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
