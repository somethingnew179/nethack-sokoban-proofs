import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0736_0_checked : (List.range' 376832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0736_1_checked : (List.range' 376960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0736_2_checked : (List.range' 377088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0736_3_checked : (List.range' 377216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0736_range (index : Nat) (lower : 376832 ≤ index) (upper : index < 377344) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 377088 then
    if cut : index < 376960 then
      exact segment_sound _ 376832 128 Update0736_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376960 128 Update0736_1_checked index (by omega) (by omega)
  else
    if cut : index < 377216 then
      exact segment_sound _ 377088 128 Update0736_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 377216 128 Update0736_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
