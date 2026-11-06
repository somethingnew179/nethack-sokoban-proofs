import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0343_0_checked : (List.range' 175616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0343_1_checked : (List.range' 175744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0343_2_checked : (List.range' 175872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0343_3_checked : (List.range' 176000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0343_range (index : Nat) (lower : 175616 ≤ index) (upper : index < 176128) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 175872 then
    if cut : index < 175744 then
      exact segment_sound _ 175616 128 Update0343_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 175744 128 Update0343_1_checked index (by omega) (by omega)
  else
    if cut : index < 176000 then
      exact segment_sound _ 175872 128 Update0343_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 176000 128 Update0343_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
