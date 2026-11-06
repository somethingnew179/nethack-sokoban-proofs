import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0317_0_checked : (List.range' 162304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0317_1_checked : (List.range' 162432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0317_2_checked : (List.range' 162560 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0317_3_checked : (List.range' 162688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0317_range (index : Nat) (lower : 162304 ≤ index) (upper : index < 162816) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 162560 then
    if cut : index < 162432 then
      exact segment_sound _ 162304 128 Update0317_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 162432 128 Update0317_1_checked index (by omega) (by omega)
  else
    if cut : index < 162688 then
      exact segment_sound _ 162560 128 Update0317_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 162688 128 Update0317_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
