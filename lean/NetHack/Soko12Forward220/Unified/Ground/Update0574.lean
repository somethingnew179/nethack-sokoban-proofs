import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0574_0_checked : (List.range' 293888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0574_1_checked : (List.range' 294016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0574_2_checked : (List.range' 294144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0574_3_checked : (List.range' 294272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0574_range (index : Nat) (lower : 293888 ≤ index) (upper : index < 294400) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 294144 then
    if cut : index < 294016 then
      exact segment_sound _ 293888 128 Update0574_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294016 128 Update0574_1_checked index (by omega) (by omega)
  else
    if cut : index < 294272 then
      exact segment_sound _ 294144 128 Update0574_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294272 128 Update0574_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
