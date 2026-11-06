import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0579_0_checked : (List.range' 296448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0579_1_checked : (List.range' 296576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0579_2_checked : (List.range' 296704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0579_3_checked : (List.range' 296832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0579_range (index : Nat) (lower : 296448 ≤ index) (upper : index < 296960) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 296704 then
    if cut : index < 296576 then
      exact segment_sound _ 296448 128 Update0579_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296576 128 Update0579_1_checked index (by omega) (by omega)
  else
    if cut : index < 296832 then
      exact segment_sound _ 296704 128 Update0579_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296832 128 Update0579_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
