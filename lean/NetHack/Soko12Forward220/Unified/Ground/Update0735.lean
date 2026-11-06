import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0735_0_checked : (List.range' 376320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0735_1_checked : (List.range' 376448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0735_2_checked : (List.range' 376576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0735_3_checked : (List.range' 376704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0735_range (index : Nat) (lower : 376320 ≤ index) (upper : index < 376832) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 376576 then
    if cut : index < 376448 then
      exact segment_sound _ 376320 128 Update0735_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376448 128 Update0735_1_checked index (by omega) (by omega)
  else
    if cut : index < 376704 then
      exact segment_sound _ 376576 128 Update0735_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376704 128 Update0735_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
