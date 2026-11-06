import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0548_0_checked : (List.range' 280576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0548_1_checked : (List.range' 280704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0548_2_checked : (List.range' 280832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0548_3_checked : (List.range' 280960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0548_range (index : Nat) (lower : 280576 ≤ index) (upper : index < 281088) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 280832 then
    if cut : index < 280704 then
      exact segment_sound _ 280576 128 Update0548_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 280704 128 Update0548_1_checked index (by omega) (by omega)
  else
    if cut : index < 280960 then
      exact segment_sound _ 280832 128 Update0548_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 280960 128 Update0548_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
