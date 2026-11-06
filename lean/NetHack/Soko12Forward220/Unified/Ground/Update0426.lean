import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0426_0_checked : (List.range' 218112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0426_1_checked : (List.range' 218240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0426_2_checked : (List.range' 218368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0426_3_checked : (List.range' 218496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0426_range (index : Nat) (lower : 218112 ≤ index) (upper : index < 218624) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 218368 then
    if cut : index < 218240 then
      exact segment_sound _ 218112 128 Update0426_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 218240 128 Update0426_1_checked index (by omega) (by omega)
  else
    if cut : index < 218496 then
      exact segment_sound _ 218368 128 Update0426_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 218496 128 Update0426_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
