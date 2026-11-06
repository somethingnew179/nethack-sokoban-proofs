import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0392_0_checked : (List.range' 200704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0392_1_checked : (List.range' 200832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0392_2_checked : (List.range' 200960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0392_3_checked : (List.range' 201088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0392_range (index : Nat) (lower : 200704 ≤ index) (upper : index < 201216) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 200960 then
    if cut : index < 200832 then
      exact segment_sound _ 200704 128 Update0392_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 200832 128 Update0392_1_checked index (by omega) (by omega)
  else
    if cut : index < 201088 then
      exact segment_sound _ 200960 128 Update0392_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 201088 128 Update0392_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
