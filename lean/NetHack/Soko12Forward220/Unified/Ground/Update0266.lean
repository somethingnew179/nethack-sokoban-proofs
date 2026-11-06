import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0266_0_checked : (List.range' 136192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0266_1_checked : (List.range' 136320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0266_2_checked : (List.range' 136448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0266_3_checked : (List.range' 136576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0266_range (index : Nat) (lower : 136192 ≤ index) (upper : index < 136704) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 136448 then
    if cut : index < 136320 then
      exact segment_sound _ 136192 128 Update0266_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 136320 128 Update0266_1_checked index (by omega) (by omega)
  else
    if cut : index < 136576 then
      exact segment_sound _ 136448 128 Update0266_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 136576 128 Update0266_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
