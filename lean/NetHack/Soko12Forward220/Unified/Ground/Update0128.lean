import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0128_0_checked : (List.range' 65536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0128_1_checked : (List.range' 65664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0128_2_checked : (List.range' 65792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0128_3_checked : (List.range' 65920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0128_range (index : Nat) (lower : 65536 ≤ index) (upper : index < 66048) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 65792 then
    if cut : index < 65664 then
      exact segment_sound _ 65536 128 Update0128_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 65664 128 Update0128_1_checked index (by omega) (by omega)
  else
    if cut : index < 65920 then
      exact segment_sound _ 65792 128 Update0128_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 65920 128 Update0128_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
