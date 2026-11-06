import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0581_0_checked : (List.range' 297472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0581_1_checked : (List.range' 297600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0581_2_checked : (List.range' 297728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0581_3_checked : (List.range' 297856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0581_range (index : Nat) (lower : 297472 ≤ index) (upper : index < 297984) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 297728 then
    if cut : index < 297600 then
      exact segment_sound _ 297472 128 Update0581_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297600 128 Update0581_1_checked index (by omega) (by omega)
  else
    if cut : index < 297856 then
      exact segment_sound _ 297728 128 Update0581_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297856 128 Update0581_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
