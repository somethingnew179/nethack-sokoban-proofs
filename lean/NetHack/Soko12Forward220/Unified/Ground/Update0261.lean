import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0261_0_checked : (List.range' 133632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0261_1_checked : (List.range' 133760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0261_2_checked : (List.range' 133888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0261_3_checked : (List.range' 134016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0261_range (index : Nat) (lower : 133632 ≤ index) (upper : index < 134144) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 133888 then
    if cut : index < 133760 then
      exact segment_sound _ 133632 128 Update0261_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 133760 128 Update0261_1_checked index (by omega) (by omega)
  else
    if cut : index < 134016 then
      exact segment_sound _ 133888 128 Update0261_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 134016 128 Update0261_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
