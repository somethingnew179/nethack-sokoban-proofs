import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0468_0_checked : (List.range' 239616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0468_1_checked : (List.range' 239744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0468_2_checked : (List.range' 239872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0468_3_checked : (List.range' 240000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0468_range (index : Nat) (lower : 239616 ≤ index) (upper : index < 240128) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 239872 then
    if cut : index < 239744 then
      exact segment_sound _ 239616 128 Update0468_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 239744 128 Update0468_1_checked index (by omega) (by omega)
  else
    if cut : index < 240000 then
      exact segment_sound _ 239872 128 Update0468_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 240000 128 Update0468_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
