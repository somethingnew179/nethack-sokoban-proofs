import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0294_0_checked : (List.range' 150528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0294_1_checked : (List.range' 150656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0294_2_checked : (List.range' 150784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0294_3_checked : (List.range' 150912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0294_range (index : Nat) (lower : 150528 ≤ index) (upper : index < 151040) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 150784 then
    if cut : index < 150656 then
      exact segment_sound _ 150528 128 Update0294_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 150656 128 Update0294_1_checked index (by omega) (by omega)
  else
    if cut : index < 150912 then
      exact segment_sound _ 150784 128 Update0294_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 150912 128 Update0294_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
