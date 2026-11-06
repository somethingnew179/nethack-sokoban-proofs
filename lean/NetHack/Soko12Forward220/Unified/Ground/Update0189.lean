import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0189_0_checked : (List.range' 96768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0189_1_checked : (List.range' 96896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0189_2_checked : (List.range' 97024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0189_3_checked : (List.range' 97152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0189_range (index : Nat) (lower : 96768 ≤ index) (upper : index < 97280) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 97024 then
    if cut : index < 96896 then
      exact segment_sound _ 96768 128 Update0189_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 96896 128 Update0189_1_checked index (by omega) (by omega)
  else
    if cut : index < 97152 then
      exact segment_sound _ 97024 128 Update0189_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 97152 128 Update0189_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
