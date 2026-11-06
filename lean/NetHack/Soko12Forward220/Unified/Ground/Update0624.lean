import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0624_0_checked : (List.range' 319488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0624_1_checked : (List.range' 319616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0624_2_checked : (List.range' 319744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0624_3_checked : (List.range' 319872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0624_range (index : Nat) (lower : 319488 ≤ index) (upper : index < 320000) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 319744 then
    if cut : index < 319616 then
      exact segment_sound _ 319488 128 Update0624_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 319616 128 Update0624_1_checked index (by omega) (by omega)
  else
    if cut : index < 319872 then
      exact segment_sound _ 319744 128 Update0624_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 319872 128 Update0624_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
