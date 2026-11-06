import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0406_0_checked : (List.range' 207872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0406_1_checked : (List.range' 208000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0406_2_checked : (List.range' 208128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0406_3_checked : (List.range' 208256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0406_range (index : Nat) (lower : 207872 ≤ index) (upper : index < 208384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 208128 then
    if cut : index < 208000 then
      exact segment_sound _ 207872 128 Update0406_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 208000 128 Update0406_1_checked index (by omega) (by omega)
  else
    if cut : index < 208256 then
      exact segment_sound _ 208128 128 Update0406_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 208256 128 Update0406_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
