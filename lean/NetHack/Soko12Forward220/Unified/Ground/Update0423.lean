import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0423_0_checked : (List.range' 216576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0423_1_checked : (List.range' 216704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0423_2_checked : (List.range' 216832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0423_3_checked : (List.range' 216960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0423_range (index : Nat) (lower : 216576 ≤ index) (upper : index < 217088) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 216832 then
    if cut : index < 216704 then
      exact segment_sound _ 216576 128 Update0423_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216704 128 Update0423_1_checked index (by omega) (by omega)
  else
    if cut : index < 216960 then
      exact segment_sound _ 216832 128 Update0423_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216960 128 Update0423_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
