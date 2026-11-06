import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0665_0_checked : (List.range' 340480 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0665_1_checked : (List.range' 340608 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0665_2_checked : (List.range' 340736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0665_3_checked : (List.range' 340864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0665_range (index : Nat) (lower : 340480 ≤ index) (upper : index < 340992) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 340736 then
    if cut : index < 340608 then
      exact segment_sound _ 340480 128 Update0665_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 340608 128 Update0665_1_checked index (by omega) (by omega)
  else
    if cut : index < 340864 then
      exact segment_sound _ 340736 128 Update0665_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 340864 128 Update0665_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
