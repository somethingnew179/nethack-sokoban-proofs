import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0388_0_checked : (List.range' 198656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0388_1_checked : (List.range' 198784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0388_2_checked : (List.range' 198912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0388_3_checked : (List.range' 199040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0388_range (index : Nat) (lower : 198656 ≤ index) (upper : index < 199168) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 198912 then
    if cut : index < 198784 then
      exact segment_sound _ 198656 128 Update0388_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 198784 128 Update0388_1_checked index (by omega) (by omega)
  else
    if cut : index < 199040 then
      exact segment_sound _ 198912 128 Update0388_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 199040 128 Update0388_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
