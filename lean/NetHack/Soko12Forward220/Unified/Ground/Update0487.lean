import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0487_0_checked : (List.range' 249344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0487_1_checked : (List.range' 249472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0487_2_checked : (List.range' 249600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0487_3_checked : (List.range' 249728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0487_range (index : Nat) (lower : 249344 ≤ index) (upper : index < 249856) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 249600 then
    if cut : index < 249472 then
      exact segment_sound _ 249344 128 Update0487_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 249472 128 Update0487_1_checked index (by omega) (by omega)
  else
    if cut : index < 249728 then
      exact segment_sound _ 249600 128 Update0487_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 249728 128 Update0487_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
