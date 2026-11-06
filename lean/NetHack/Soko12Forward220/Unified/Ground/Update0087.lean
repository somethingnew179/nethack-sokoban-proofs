import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0087_0_checked : (List.range' 44544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0087_1_checked : (List.range' 44672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0087_2_checked : (List.range' 44800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0087_3_checked : (List.range' 44928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0087_range (index : Nat) (lower : 44544 ≤ index) (upper : index < 45056) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 44800 then
    if cut : index < 44672 then
      exact segment_sound _ 44544 128 Update0087_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 44672 128 Update0087_1_checked index (by omega) (by omega)
  else
    if cut : index < 44928 then
      exact segment_sound _ 44800 128 Update0087_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 44928 128 Update0087_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
