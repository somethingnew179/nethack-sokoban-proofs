import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0030_0_checked : (List.range' 15360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0030_1_checked : (List.range' 15488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0030_2_checked : (List.range' 15616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0030_3_checked : (List.range' 15744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0030_range (index : Nat) (lower : 15360 ≤ index) (upper : index < 15872) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 15616 then
    if cut : index < 15488 then
      exact segment_sound _ 15360 128 Update0030_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 15488 128 Update0030_1_checked index (by omega) (by omega)
  else
    if cut : index < 15744 then
      exact segment_sound _ 15616 128 Update0030_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 15744 128 Update0030_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
