import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0267_0_checked : (List.range' 136704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0267_1_checked : (List.range' 136832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0267_2_checked : (List.range' 136960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0267_3_checked : (List.range' 137088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0267_range (index : Nat) (lower : 136704 ≤ index) (upper : index < 137216) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 136960 then
    if cut : index < 136832 then
      exact segment_sound _ 136704 128 Update0267_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 136832 128 Update0267_1_checked index (by omega) (by omega)
  else
    if cut : index < 137088 then
      exact segment_sound _ 136960 128 Update0267_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 137088 128 Update0267_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
