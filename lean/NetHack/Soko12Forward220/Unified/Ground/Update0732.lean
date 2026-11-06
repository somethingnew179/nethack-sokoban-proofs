import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0732_0_checked : (List.range' 374784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0732_1_checked : (List.range' 374912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0732_2_checked : (List.range' 375040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0732_3_checked : (List.range' 375168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0732_range (index : Nat) (lower : 374784 ≤ index) (upper : index < 375296) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 375040 then
    if cut : index < 374912 then
      exact segment_sound _ 374784 128 Update0732_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 374912 128 Update0732_1_checked index (by omega) (by omega)
  else
    if cut : index < 375168 then
      exact segment_sound _ 375040 128 Update0732_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 375168 128 Update0732_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
