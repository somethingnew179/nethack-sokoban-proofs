import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0136_0_checked : (List.range' 69632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0136_1_checked : (List.range' 69760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0136_2_checked : (List.range' 69888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0136_3_checked : (List.range' 70016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0136_range (index : Nat) (lower : 69632 ≤ index) (upper : index < 70144) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 69888 then
    if cut : index < 69760 then
      exact segment_sound _ 69632 128 Update0136_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 69760 128 Update0136_1_checked index (by omega) (by omega)
  else
    if cut : index < 70016 then
      exact segment_sound _ 69888 128 Update0136_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 70016 128 Update0136_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
