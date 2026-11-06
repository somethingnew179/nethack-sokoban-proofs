import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0158_0_checked : (List.range' 80896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0158_1_checked : (List.range' 81024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0158_2_checked : (List.range' 81152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0158_3_checked : (List.range' 81280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0158_range (index : Nat) (lower : 80896 ≤ index) (upper : index < 81408) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 81152 then
    if cut : index < 81024 then
      exact segment_sound _ 80896 128 Update0158_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81024 128 Update0158_1_checked index (by omega) (by omega)
  else
    if cut : index < 81280 then
      exact segment_sound _ 81152 128 Update0158_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 81280 128 Update0158_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
